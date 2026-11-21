/-
bergdb 030-37: the leaf join loop against the deletes counted by Java.
An empty or a small planned child needs at least one counted delete. The
same delete is not charged for both. Empty children and joins together
therefore remove at most nd of the parent's original children.
-/
import Contract.Proof.DnbLeafJoins

namespace Contract.PE

open DNB PeProof

variable {i : Time} {s : Tree}

/-- The syntactic form of a successfully planned segment leaf. -/
theorem plan_leaf_form {cf : Cfg} {f x g : Nat} {ops : List Op} {acc acc' : Acc} {v : VN}
    (hp : plan cf i s f x g 0 ops acc = some (v, acc')) :
    ∃ n es, getKey s x = some n ∧ (∀ e ∈ es, ∃ y, e.2 = .old y) ∧
      v = .node (some x) g 0 false es (es.flatMap (fun e => ents e.1 e.2))
        (decideNode cf i (some n) false (es.flatMap (fun e => ents e.1 e.2))) := by
  cases f with
  | zero => simp [plan] at hp
  | succ f =>
    rw [plan.eq_def] at hp
    simp only [beq_self_eq_true, ↓reduceIte] at hp
    cases hk : getKey s x with
    | none => rw [hk] at hp; cases hp
    | some n =>
      rw [hk] at hp
      simp only at hp
      cases ha : applyGroups cf i s f g (live n.ks) ((ops.map (segAt g)).eraseDups) ops acc with
      | none => rw [ha] at hp; cases hp
      | some q =>
        obtain ⟨es, acc1⟩ := q
        rw [ha] at hp
        simp only at hp
        unfold mkNode at hp
        simp only [beq_self_eq_true, ↓reduceIte, hk, Option.some.injEq, Prod.mk.injEq] at hp
        obtain ⟨rfl, rfl⟩ := hp
        refine ⟨n, es.map (fun e => (e.1, VN.old e.2)), rfl, ?_, rfl⟩
        intro e he
        obtain ⟨q, _, rfl⟩ := List.mem_map.mp he
        exact ⟨q.2, rfl⟩

/-- A leaf plan satisfying the existing induction statement is one of the
loop's leaves; an unchanged plan retains the old fill. -/
theorem plan_joinLeaf {b G H : Nat} {f x g fs : Nat} {ops : List Op} {acc acc' : Acc} {v : VN}
    (hp : plan (Cfg.java b G H) i s f x g 0 ops acc = some (v, acc'))
    (hc : PlanSpecD b s g 0 x false v acc acc' (sbPlan b s fs x g ops false))
    (hks : ∀ n, getKey s x = some n → n.ks.length ≤ b)
    (hfill : ∀ n, getKey s x = some n → (Cfg.java b G H).m ≤ (live n.ks).length) :
    JoinLeaf b G H i s v := by
  obtain ⟨n, es, hk, hpay, rfl⟩ := plan_leaf_form hp
  obtain ⟨n', es', F', dec', hk', heq, _, _, hgrow⟩ := hc.shape
  change getKey s x = some n' at hk'
  rw [hk] at hk'; cases hk'
  cases heq
  apply JoinLeaf.planned (hks n hk) hpay hgrow
  intro hs
  have heq : (live n.ks).map (fun q => (q.1, some q.2)) = es.flatMap (fun e => ents e.1 e.2) := by
    unfold decideNode at hs
    simp only at hs
    split at hs
    · rename_i he; exact beq_iff_eq.mp he
    · split at hs
      · split at hs
        · split at hs <;> cases hs
        · cases hs
      · cases hs
  have hlen := congrArg List.length heq
  rw [List.length_map] at hlen
  rw [← hlen]
  exact hfill n hk

/-- Supplement `kids_drop` with the leaf forms, the unchanged child compare
values, and the joint budget for dropping empties and joining small leaves. -/
theorem kids_leaf_resources {b G H g F0 fs : Nat} (hb : 8 ≤ b)
    {lvAll : List (Nat × NodeId)} (P : Nat → NodeId → List Op → Prop)
    (hchild : ∀ f < F0, ∀ c y o acc w acc', (c, y) ∈ lvAll → o ≠ [] → P c y o →
      plan (Cfg.java b G H) i s f y g 0 o acc = some (w, acc') →
      PlanSpecD b s g 0 y false w acc acc' (sbPlan b s fs y g o false))
    (hks : ∀ c y, (c, y) ∈ lvAll → ∀ n, getKey s y = some n → n.ks.length ≤ b)
    (hfill : ∀ c y, (c, y) ∈ lvAll → ∃ n, getKey s y = some n ∧
      (Cfg.java b G H).m ≤ (live n.ks).length) :
    ∀ (lv : List (Nat × NodeId)) (os : List (List Op)) (f : Nat) (acc : Acc)
      (es : List (Nat × VN)) (acc1 : Acc), lv ⊆ lvAll →
      (∀ cy o, (cy, o) ∈ lv.zip os → P cy.1 cy.2 o) → f ≤ F0 →
      planKids (Cfg.java b G H) i s f g 1 lv os acc = some (es, acc1) →
      (∀ e ∈ es, JoinLeaf b G H i s e.2) ∧ es.map (·.1) = lv.map (·.1) ∧
      lv.length + smallLeaves (Cfg.java b G H) (kept es) ≤ (kept es).length +
        ((childRs b s fs g lv os).map (·.nd)).sum
  | _, _, 0, _, _, _, _, _, _, hp => by simp [planKids] at hp
  | [], os, f + 1, acc, es, acc1, _, _, _, hp => by
    simp only [planKids, Option.some.injEq, Prod.mk.injEq] at hp
    obtain ⟨rfl, rfl⟩ := hp
    exact ⟨by simp, rfl, by simp [kept, childRs, smallLeaves]⟩
  | (c, y) :: rest, [], f + 1, acc, es, acc1, _, _, _, hp => by simp [planKids] at hp
  | (c, y) :: rest, o :: os, f + 1, acc, es, acc1, hsub, hos, hf, hp => by
    have hmem : (c, y) ∈ lvAll := hsub List.mem_cons_self
    have hsub' : rest ⊆ lvAll := fun q hq => hsub (List.mem_cons_of_mem _ hq)
    have hos' : ∀ cy o', (cy, o') ∈ rest.zip os → P cy.1 cy.2 o' :=
      fun cy o' ho => hos cy o' (List.mem_cons_of_mem _ ho)
    obtain ⟨n, hk, hfilln⟩ := hfill c y hmem
    simp only [planKids] at hp
    split at hp
    · rename_i hoe
      cases ht : planKids (Cfg.java b G H) i s f g 1 rest os acc with
      | none => rw [ht] at hp; cases hp
      | some q =>
        obtain ⟨es', acc2⟩ := q
        rw [ht] at hp
        simp only [Option.some.injEq, Prod.mk.injEq] at hp
        obtain ⟨rfl, rfl⟩ := hp
        obtain ⟨ih1, ih2, ih3⟩ := kids_leaf_resources hb P hchild hks hfill rest os f acc es' acc2
          hsub' hos' (by omega) ht
        refine ⟨?_, by simpa using congrArg (List.cons c) ih2, ?_⟩
        · intro e he
          rcases List.mem_cons.mp he with rfl | he
          · exact JoinLeaf.old hk (hks c y hmem n hk) hfilln
          · exact ih1 e he
        · have hz : childRs b s fs g ((c, y) :: rest) (o :: os) = childRs b s fs g rest os := by
            simp [childRs, hoe]
          have hke : kept ((c, VN.old y) :: es') = (c, VN.old y) :: kept es' := by simp [kept, VN.isEmpty]
          rw [hke, smallLeaves_cons, hz]
          simp only [smallLeaf, VN.changed, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
            Nat.zero_add, List.length_cons]
          omega
    · rename_i hoe
      have hone : o ≠ [] := by simpa using hoe
      cases hpl : plan (Cfg.java b G H) i s f y g 0 o acc with
      | none => rw [hpl] at hp; cases hp
      | some q0 =>
        obtain ⟨w, acc2⟩ := q0
        rw [hpl] at hp
        simp only at hp
        cases ht : planKids (Cfg.java b G H) i s f g 1 rest os acc2 with
        | none => rw [ht] at hp; cases hp
        | some q =>
          obtain ⟨es', acc3⟩ := q
          rw [ht] at hp
          simp only [Option.some.injEq, Prod.mk.injEq] at hp
          obtain ⟨rfl, rfl⟩ := hp
          obtain ⟨ih1, ih2, ih3⟩ := kids_leaf_resources hb P hchild hks hfill rest os f acc2 es' acc3
            hsub' hos' (by omega) ht
          have hc := hchild f (by omega) c y o acc w acc2 hmem hone (hos (c,y) o List.mem_cons_self) hpl
          have hw := plan_joinLeaf hpl hc (hks c y hmem) (fun n' hn' => by
            rw [hk] at hn'; cases hn'; exact hfilln)
          refine ⟨?_, by simpa using congrArg (List.cons c) ih2, ?_⟩
          · intro e he
            rcases List.mem_cons.mp he with rfl | he
            · exact hw
            · exact ih1 e he
          · have hnd : (w.isEmpty = true ∨ smallLeaf (Cfg.java b G H) w = true) →
                1 ≤ (sbPlan b s fs y g o false).nd := by
              intro hh
              obtain ⟨n', es0, F, dec, hn', heq, _, hloss, _⟩ := hc.shape
              change getKey s y = some n' at hn'
              rw [hk] at hn'; cases hn'
              have hsize : w.size = F.length := by rw [heq]; rfl
              have hempty : w.isEmpty = true → F.length = 0 := by
                rw [heq]; simp [VN.isEmpty]
              have hm2 : 2 ≤ (Cfg.java b G H).m := by
                exact (java_params hb).1
              rcases hh with hh | hh
              · have := hempty hh; omega
              · have hh' : w.size < (Cfg.java b G H).m := by
                  unfold smallLeaf at hh
                  simp only [Bool.and_eq_true, decide_eq_true_eq] at hh
                  exact hh.2
                omega
            have hz : childRs b s fs g ((c, y) :: rest) (o :: os) =
                sbPlan b s fs y g o false :: childRs b s fs g rest os := by simp [childRs, hoe]
            rw [hz]
            simp only [List.map_cons, List.sum_cons]
            by_cases hem : w.isEmpty = true
            · have hnd1 := hnd (Or.inl hem)
              simp only [kept, List.filter_cons, hem, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
              change rest.length + 1 + smallLeaves (Cfg.java b G H) (kept es') ≤
                (kept es').length + ((sbPlan b s fs y g o false).nd +
                  ((childRs b s fs g rest os).map (·.nd)).sum)
              omega
            · have hem0 : w.isEmpty = false := by simpa using hem
              have hke : kept ((c, w) :: es') = (c, w) :: kept es' := by simp [kept, hem0]
              rw [hke, smallLeaves_cons]
              simp only [List.length_cons]
              split
              · rename_i hs
                have hnd1 := hnd (Or.inr hs)
                omega
              · omega

theorem ents_head_cv (c : Nat) (v : VN) : (ents c v).head?.map (·.1) = some c := by
  cases v with
  | old y => rfl
  | node base g h j es F dec =>
    cases dec with
    | same => cases base <;> rfl
    | append => cases base <;> rfl
    | parts k =>
      simp only [ents]
      split
      · exact partEnts_head c F k j
      · rfl

theorem entries_head (es : List (Nat × VN)) :
    (entries es).head?.map (·.1) = es.head?.map (·.1) := by
  cases es with
  | nil => rfl
  | cons e es =>
    rw [entries_cons, List.head?_append_of_ne_nil _ (ents_ne _ _)]
    exact ents_head_cv _ _

theorem entries_any_cv {es : List (Nat × VN)} {c : Nat} (hc : c ∈ es.map (·.1)) :
    (entries es).any (fun e => e.1 == c) = true := by
  induction es with
  | nil => simp at hc
  | cons e es ih =>
    rcases List.mem_cons.mp hc with hc | hc
    · rw [hc, entries_cons, List.any_append, ents_any_head]; rfl
    · rw [entries_cons, List.any_append, ih hc, Bool.or_true]

theorem removed_le_of_sublist {lv : List (Nat × NodeId)} {cs : List Nat}
    {F : List (Nat × Option NodeId)} (hs : cs.Sublist (lv.map (·.1)))
    (hk : ∀ c ∈ cs, F.any (fun e => e.1 == c) = true) :
    (removedCvs lv F).length + cs.length ≤ lv.length := by
  let p : Nat → Bool := fun c => F.any (fun e => e.1 == c)
  have hsub := hs.filter p
  rw [List.filter_eq_self.mpr hk] at hsub
  have hlen := hsub.length_le
  have partition (L : List (Nat × NodeId)) : (L.filter (fun e => !p e.1)).length +
      (L.filter (fun e => p e.1)).length = L.length := by
    induction L with
    | nil => rfl
    | cons e L ih => cases hp : p e.1 <;> simp [hp] <;> omega
  have hpartition := partition lv
  have heq : ((lv.map (·.1)).filter p).length = (lv.filter (fun e => p e.1)).length := by
    rw [List.filter_map, List.length_map]; rfl
  rw [heq] at hlen
  simpa only [removedCvs, List.length_map] using (show (lv.filter (fun e => !p e.1)).length +
    cs.length ≤ lv.length from by omega)

theorem JoinLeaf.ents_length {b G H : Nat} (hb : 8 ≤ b) {v : VN}
    (hv : JoinLeaf b G H i s v) (c : Nat) : (ents c v).length ≤ 1 + noneCount c v := by
  cases hv with
  | old => simp [ents, noneCount]
  | @planned y g n es hks _ hlen _ =>
    exact (decide_facts (G := G) (H := H) (i := i) (g := g) (h := 0) (y := y) (c := c)
      (es := es) hb hks hlen).2.2.2.2.2
  | @joined g es _ =>
    have hj := joined_facts (b := b) (G := G) (H := H) (g := g) (h := 0) (c := c)
      (es := es) (F := es.flatMap (fun e => ents e.1 e.2))
    rw [hj.2.2.1, hj.2.2.2]; omega

theorem entries_length_le_none {b G H : Nat} (hb : 8 ≤ b) {es : List (Nat × VN)}
    (hv : ∀ e ∈ es, JoinLeaf b G H i s e.2) :
    (entries es).length ≤ es.length + newEntries es := by
  induction es with
  | nil => simp [entries, newEntries]
  | cons e es ih =>
    have he := (hv e List.mem_cons_self).ents_length hb e.1
    have ht := ih (fun e he => hv e (List.mem_cons_of_mem _ he))
    rw [entries_cons, List.length_append, newEntries_cons]
    simp only [List.length_cons]
    omega

theorem none_entries_le_added (lb : List (Nat × NodeId)) : ∀ F : List (Nat × Option NodeId),
    (F.filter (fun e => e.2.isNone)).length ≤ (F.filter (isAdded lb)).length
  | [] => by simp
  | e :: F => by
    have ih := none_entries_le_added lb F
    cases he : e.2 with
    | none => simp [isAdded, he]; omega
    | some y =>
      simp only [List.filter_cons, he, Option.isNone_some, Bool.false_eq_true, ↓reduceIte]
      split
      · simp_all; omega
      · simp_all

theorem none_renameHead (c : Nat) (F : List (Nat × Option NodeId)) :
    ((renameHead c F).filter (fun e => e.2.isNone)).length =
      (F.filter (fun e => e.2.isNone)).length := by
  cases F with
  | nil => rfl
  | cons e F => simp only [renameHead, List.filter_cons]; split <;> rfl

/-- Full rebalance of segment leaves, including empty-child removal and
renaming the parent's first separator. The estimates are exactly those
needed by the original dirty-bound node induction. -/
theorem rebalance_leaf_budget {b G H : Nat} (hb : 8 ≤ b) {f g nd U : Nat}
    {es es2 : List (Nat × VN)} {lv : List (Nat × NodeId)}
    (hv : ∀ e ∈ es, JoinLeaf b G H i s e.2)
    (hcvs : es.map (·.1) = lv.map (·.1))
    (hbudget : lv.length + smallLeaves (Cfg.java b G H) (kept es) ≤ (kept es).length + nd)
    (hadded : addedEntries lv (kept es) ≤ U)
    (hsame : nd = 0 → addedEntries lv (kept es) = 0 →
      entries (kept es) = lv.map (fun q => (q.1, some q.2)))
    (hhead : lv.head?.map (·.1) = some 0) (hsort : lv.Pairwise CvLtA)
    (hr : rebalance (Cfg.java b G H) i s (f + 1) g 0 es = some es2) :
    vcostL es2 ≤ vcostL (kept es) + 2 * nd ∧
      lv.length ≤ (renameHead 0 (entries es2)).length + nd ∧
      (removedCvs lv (renameHead 0 (entries es2))).length +
        ((renameHead 0 (entries es2)).filter (isAdded lv)).length ≤ 4 * nd + U ∧
      (renameHead 0 (entries es2)).length ≤ lv.length +
        ((renameHead 0 (entries es2)).filter (isAdded lv)).length ∧
      (4 * nd + U = 0 → lv.map (fun q => (q.1, some q.2)) = renameHead 0 (entries es2)) := by
  have hm := (java_params (G := G) (H := H) hb).2.2.2.2.2.2
  change (if !(Cfg.java b G H).merges then some (kept es) else
    joinLoop (Cfg.java b G H) i s g 0 (fun J => rebalance (Cfg.java b G H) i s f g (0 - 1) J)
      ((kept es).length + 1) (kept es)) = some es2 at hr
  simp only [hm, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hr
  have hkv : ∀ e ∈ kept es, JoinLeaf b G H i s e.2 :=
    fun e he => hv e (List.mem_of_mem_filter he)
  obtain ⟨j, hv2, hcost, _, hlen, hsm, hcsub, hhd, hA⟩ := joinLoop_leaf_account hb _ _ _ hkv hr
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
  have hElen := entries_length_le_none hb hv2
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
    have hsmall0 : smallLeaves (Cfg.java b G H) (kept es) = 0 := by omega
    have hfind : findSmall (Cfg.java b G H) (kept es) = none := by
      unfold findSmall
      rw [Option.map_eq_none_iff, List.find?_eq_none]
      intro p hp
      have hem : p.1 ∈ kept es := List.mem_of_getElem? (mem_zipIdx_get hp).2
      have hn : smallLeaf (Cfg.java b G H) p.1.2 = false := by
        by_contra hh
        have ht : p.1 ∈ (kept es).filter (fun e => smallLeaf (Cfg.java b G H) e.2) := by
          exact List.mem_filter.mpr ⟨hem, by simpa using hh⟩
        have hl : 0 < smallLeaves (Cfg.java b G H) (kept es) := List.length_pos_of_mem ht
        omega
      change ¬smallLeaf (Cfg.java b G H) p.1.2 = true
      rw [hn]; decide
    have hstop : es2 = kept es := by
      rw [joinLoop] at hr
      split at hr
      · exact (Option.some.inj hr).symm
      · rw [hfind] at hr
        exact (Option.some.inj hr).symm
    rw [hstop]
    exact (hsame hnd (by omega)).symm

end Contract.PE
