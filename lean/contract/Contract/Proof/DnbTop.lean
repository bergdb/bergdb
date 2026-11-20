/-
bergdb 030-29: a transaction of PE against Java's count, for puts: the key
nodes PE writes are at most `sbTop`, Java's count of the transaction as one
recursion over the tree (`pe_keyWrites_puts`).
-/
import Contract.Proof.DnbPlan

namespace Contract.PE

open DNB PeProof

variable {i : Time} {s : Tree}

theorem keyWrites_eq_kw (acc : Acc) : keyWrites acc.ws = kw acc := rfl

/-- **PE's key writes for a transaction of puts are at most Java's count.**
From a state PE keeps whose tree meets the writer's fill rules (the trace
checker's `shapeFaults`), for Java's parameters at node size b ≥ 8. -/
theorem pe_keyWrites_puts {b G H : Nat} (hb : 8 ≤ b) {t : Time} {tp : Top} {next : NodeId}
    {ops : List Op} {o : Out} (hI : Inv (Cfg.java b G H) t s tp next)
    (hsf : shapeFaults ⟨(Cfg.java b G H).H, (Cfg.java b G H).m, (Cfg.java b G H).theta⟩ s = [])
    (hputs : ∀ op ∈ ops, opDel op = false) (hne : ops ≠ [])
    (hw : peTx (Cfg.java b G H) i s tp next ops = some o) :
    keyWrites o.ws ≤ sbTop b s ops := by
  have hdrop : dropNoops (Cfg.java b G H) ops = ops := by
    unfold dropNoops
    rw [List.filter_eq_self]
    intro op hop
    have := hputs op hop
    cases op with
    | put k v => rfl
    | del k => simp [opDel] at this
  unfold peTx at hw
  simp only [hdrop] at hw
  split at hw
  · cases hw
  · rename_i hok
    have hok' : opsOk (Cfg.java b G H) ops = true := by simpa using hok
    obtain ⟨r, hr, hsh⟩ := hI.shaped
    rw [hr] at hw
    simp only at hw
    obtain ⟨n, hobj, hgk, hlev, hleaf, _, _⟩ := shaped_getKey hsh
    rw [hgk] at hw
    simp only at hw
    have hht : (Cfg.java b G H).htOf n.level = htIn (Cfg.java b G H) s r := by simp [htIn, hobj]
    rw [hht] at hw
    cases hpl : plan (Cfg.java b G H) i s fuel r 0 (htIn (Cfg.java b G H) s r) ops ⟨[], next⟩ with
    | none => rw [hpl] at hw; cases hw
    | some q =>
      obtain ⟨v, acc⟩ := q
      rw [hpl] at hw
      simp only at hw
      have hgood : Good s r 0 none := good_of_invOk hr hI.inv
      have hfill : Filled (Cfg.java b G H) s true r := filled_of_shapeFaults hsf hr
      have hpa : PutsAt 0 ops := by
        intro op hop
        have h1 : keyOk (Cfg.java b G H) op.key = true := by
          unfold opsOk at hok'; exact List.all_eq_true.mp hok' op hop
        refine ⟨hputs op hop, ?_, keyOk_pos h1⟩
        simp only [keyOk, Bool.and_eq_true] at h1
        exact h1.1
      have hp := (plan_tree_puts (i := i) (s := s) (G := G) (H := H) hb fuel).1 r 0 _ ops ⟨[], next⟩ v acc
        true (s.fuel r) hsh ⟨0, none, hgood⟩ hfill hpa hne le_rfl hpl
      obtain ⟨n', es, Fl, dec, hgk', rfl, hdec, hlen, hFne⟩ := hp.shape
      have hgkD : DNB.getKey s r = some n := hgk
      rw [hgkD] at hgk'
      obtain rfl : n = n' := by injection hgk'
      have hF1 : htIn (Cfg.java b G H) s r ≠ 0 → Fl.length ≠ 1 := by
        intro h0
        have hl : n.leaf = false := by rw [hleaf]; simpa using h0
        have := (filled_key hfill hobj).1 hl rfl
        omega
      split at hw
      · rename_i rv hset
        obtain ⟨v', hv, hv', _⟩ := settle_chain (i := i) (s := s) hb fuel (some r) _ false es Fl dec _
          hFne hF1 hset
        cases hv
        split at hw
        · rename_i c r' acc2 hem
          have hkw := emit_kw rv acc _ acc2 hem
          have hk := hp.kw
          have hra : raOf b dec ≤ rootT b (sbPlan b s (s.fuel r) r 0 ops true) true := by
            cases dec with
            | parts k =>
              obtain ⟨hov, hkp⟩ := hdec k rfl
              simp only [raOf, rootT, true_and, Nat.pos_iff_ne_zero.mp hov, ne_eq, not_false_eq_true,
                ↓reduceIte]
              split
              · exact le_max_of_le_right (rootsAbove_mono hb hkp)
              · exact Nat.zero_le _
            | same => simp [raOf]
            | append => simp [raOf]
          have hws : o.ws = acc2.ws := by
            split at hw
            · simp only [Option.some.injEq] at hw; rw [← hw]
            · simp only [Option.some.injEq] at hw; rw [← hw]; rfl
          rw [hws, keyWrites_eq_kw]
          have h0 : kw (⟨[], next⟩ : Acc) = 0 := rfl
          simp only [sbTop, hr]
          rw [ite_eq_right (by simpa using hne)]
          omega
        · cases hw
      · cases hw

/-! ## No operations -/

theorem route_nil {β : Type} (cv : Op → Nat) : ∀ (lv : List (Nat × β)),
    route cv lv [] = lv.map (fun _ => [])
  | [] => rfl
  | [_] => rfl
  | _ :: (c', y) :: r => by
    simp only [route, List.filter_nil, List.map_cons]
    rw [route_nil cv ((c', y) :: r)]
    simp

theorem dnb_planKids_nil {g h : Nat} : ∀ (lv : List (Nat × NodeId)) (f : Nat) (acc : Acc)
    (es : List (Nat × VN)) (acc' : Acc),
    planKids cf i s f g h lv (lv.map (fun _ => [])) acc = some (es, acc') →
    es = lv.map (fun e => (e.1, VN.old e.2)) ∧ acc' = acc
  | _, 0, _, _, _, hp => by simp [planKids] at hp
  | [], f + 1, acc, es, acc', hp => by
    simp only [List.map_nil, planKids, Option.some.injEq, Prod.mk.injEq] at hp
    exact ⟨hp.1.symm, hp.2.symm⟩
  | (c, y) :: rest, f + 1, acc, es, acc', hp => by
    simp only [List.map_cons, planKids, List.isEmpty_nil, ↓reduceIte] at hp
    cases hk : planKids cf i s f g h rest (rest.map (fun _ => [])) acc with
    | none => rw [hk] at hp; cases hp
    | some q =>
      obtain ⟨es', acc2⟩ := q
      rw [hk] at hp
      simp only [Option.some.injEq, Prod.mk.injEq] at hp
      obtain ⟨rfl, rfl⟩ := hp
      obtain ⟨h1, h2⟩ := dnb_planKids_nil rest f acc es' acc2 hk
      exact ⟨by rw [h1]; rfl, h2⟩

/-- plan with no operations keeps the node as it was. -/
theorem plan_nil {b G H : Nat} {x : NodeId} {g h : Nat} {acc : Acc} {v : VN} {acc' : Acc} {f : Nat}
    {n : KNode} (hsh : Shaped (Cfg.java b G H) s g h x) (hgk0 : getKey s x = some n)
    (hp : plan (Cfg.java b G H) i s f x g h [] acc = some (v, acc')) :
    acc' = acc ∧ ∃ es, v = .node (some x) g h false es
      ((live n.ks).map (fun q => (q.1, some q.2))) .same ∧ vcost v = 0 := by
  obtain ⟨n', hobj, hgk, hlev, hleaf, _, _⟩ := shaped_getKey hsh
  rw [hgk0] at hgk
  obtain rfl : n = n' := by injection hgk
  obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := by
    cases f with
    | zero => simp [plan] at hp
    | succ f => exact ⟨f, rfl⟩
  rw [plan.eq_def] at hp
  simp only at hp
  rw [hgk0] at hp
  simp only at hp
  have hsame : ∀ F : List (Nat × Option NodeId),
      F = (live n.ks).map (fun q => (q.1, some q.2)) →
      decideNode (Cfg.java b G H) i (some n) false F = .same := by
    intro F hF; subst hF; simp [decideNode]
  cases h with
  | zero =>
    simp only [beq_self_eq_true, ↓reduceIte] at hp
    have hag : applyGroups (Cfg.java b G H) i s f g (live n.ks) (List.map (segAt g) []).eraseDups [] acc =
        if f = 0 then none else some (live n.ks, acc) := by
      cases f with
      | zero => simp [applyGroups]
      | succ f => simp [applyGroups]
    rw [hag] at hp
    split at hp
    · cases hp
    · rename_i es1 acc1 heq
      have hh : es1 = live n.ks ∧ acc1 = acc := by
        split at heq
        · cases heq
        · simp only [Option.some.injEq, Prod.mk.injEq] at heq
          exact ⟨heq.1.symm, heq.2.symm⟩
      obtain ⟨rfl, rfl⟩ := hh
      unfold mkNode at hp
      simp only [beq_self_eq_true, ↓reduceIte] at hp
      rw [hgk0] at hp
      simp only [Option.some.injEq, Prod.mk.injEq] at hp
      obtain ⟨rfl, rfl⟩ := hp
      rw [flatMap_ents_old, hsame _ rfl]
      exact ⟨rfl, _, rfl, by simp [vcost, dcost, vcostL_old]⟩
  | succ h =>
    simp only [Nat.add_one_ne_zero, beq_iff_eq, ↓reduceIte, Nat.add_sub_cancel, route_nil] at hp
    obtain ⟨hhead, _⟩ := shaped_inner hsh hobj
    cases hk : planKids (Cfg.java b G H) i s f g (h + 1) (live n.ks) ((live n.ks).map (fun _ => [])) acc with
    | none => rw [hk] at hp; cases hp
    | some q =>
      obtain ⟨es, acc1⟩ := q
      rw [hk] at hp
      simp only at hp
      obtain ⟨rfl, rfl⟩ := dnb_planKids_nil (live n.ks) f acc es acc1 hk
      cases hrb : rebalance (Cfg.java b G H) i s (f + 1) g h ((live n.ks).map (fun e => (e.1, VN.old e.2))) with
      | none => rw [hrb] at hp; cases hp
      | some es2 =>
        rw [hrb] at hp
        simp only at hp
        have hes2 := rebalance_id (fun e he => by
          rw [List.mem_map] at he
          obtain ⟨q, _, rfl⟩ := he
          exact ⟨rfl, fun h => by simp [VN.changed] at h⟩) hrb
        subst hes2
        have hesh : ((live n.ks).map (fun e => (e.1, VN.old e.2))).head?.map (·.1) = some 0 := by
          rw [List.head?_map, Option.map_map]; rw [← hhead]; rfl
        have hFh : (((live n.ks).map (fun e => (e.1, VN.old e.2))).flatMap (fun e => ents e.1 e.2)).head?.map
            (·.1) = some 0 := by
          rw [flatMap_ents_old, List.head?_map, Option.map_map]; rw [← hhead]; rfl
        unfold mkNode at hp
        simp only [Nat.add_one_ne_zero, beq_iff_eq, ↓reduceIte, renameHead_of_head hesh] at hp
        rw [hgk0, renameHead_of_head hFh] at hp
        simp only [Option.some.injEq, Prod.mk.injEq] at hp
        obtain ⟨rfl, rfl⟩ := hp
        rw [flatMap_ents_old, hsame _ rfl]
        exact ⟨rfl, _, rfl, by simp [vcost, dcost, vcostL_old]⟩

/-- **A transaction without operations writes no key node.** -/
theorem pe_keyWrites_nil {b G H : Nat} {t : Time} {tp : Top} {next : NodeId} {o : Out}
    (hI : Inv (Cfg.java b G H) t s tp next)
    (hsf : shapeFaults ⟨(Cfg.java b G H).H, (Cfg.java b G H).m, (Cfg.java b G H).theta⟩ s = [])
    (hw : peTx (Cfg.java b G H) i s tp next [] = some o) : keyWrites o.ws = 0 := by
  unfold peTx at hw
  simp only [dropNoops, List.filter_nil, opsOk, List.all_nil, Bool.not_true, Bool.false_eq_true,
    ↓reduceIte] at hw
  obtain ⟨r, hr, hsh⟩ := hI.shaped
  rw [hr] at hw
  simp only at hw
  obtain ⟨n, hobj, hgk, hlev, hleaf, _, _⟩ := shaped_getKey hsh
  rw [hgk] at hw
  simp only at hw
  cases hpl : plan (Cfg.java b G H) i s fuel r 0 ((Cfg.java b G H).htOf n.level) [] ⟨[], next⟩ with
  | none => rw [hpl] at hw; cases hw
  | some q =>
    obtain ⟨v, acc⟩ := q
    rw [hpl] at hw
    simp only at hw
    have hht : (Cfg.java b G H).htOf n.level = htIn (Cfg.java b G H) s r := by simp [htIn, hobj]
    rw [hht] at hpl
    obtain ⟨rfl, es, rfl, hv0⟩ := plan_nil hsh hgk hpl
    have hfill : Filled (Cfg.java b G H) s true r := filled_of_shapeFaults hsf hr
    -- settle keeps the root
    have hset : settleRoot (Cfg.java b G H) i s fuel 0 (.node (some r) 0 (htIn (Cfg.java b G H) s r) false es
        ((live n.ks).map (fun q => (q.1, some q.2))) .same) true =
        some (some (.node (some r) 0 (htIn (Cfg.java b G H) s r) false es
          ((live n.ks).map (fun q => (q.1, some q.2))) .same)) := by
      rw [show fuel = (fuel - 1) + 1 from rfl]
      rw [settleRoot.eq_def]
      simp only
      split
      · rename_i hemp
        simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        split
        · rfl
        · rename_i h0
          exfalso
          have hl : n.leaf = false := by rw [hleaf]; simpa using h0
          have := (filled_key hfill hobj).1 hl rfl
          simp at hemp; rw [hemp] at this; simp at this
      · split
        · rename_i h1
          exfalso
          simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq, List.length_map] at h1
          have hl : n.leaf = false := by rw [hleaf]; simpa using h1.1
          have := (filled_key hfill hobj).1 hl rfl
          omega
        · rfl
    rw [hset] at hw
    simp only at hw
    split at hw
    · rename_i c r' acc2 hem
      have hkw := emit_kw _ _ _ acc2 hem
      have hws : o.ws = acc2.ws := by
        split at hw
        · simp only [Option.some.injEq] at hw; rw [← hw]
        · simp only [Option.some.injEq] at hw; rw [← hw]; rfl
      rw [hws, keyWrites_eq_kw, hkw, hv0]
      rfl
    · cases hw

/-- **PE's key writes for a transaction of puts (none, or any number) are at
most Java's count as a recursion over the tree.** -/
theorem pe_keyWrites_le_sb_puts {b G H : Nat} (hb : 8 ≤ b) {t : Time} {tp : Top} {next : NodeId}
    {ops : List Op} {o : Out} (hI : Inv (Cfg.java b G H) t s tp next) (hfill : FillOk b H s)
    (hputs : ∀ op ∈ ops, opDel op = false)
    (hw : peTx (Cfg.java b G H) i s tp next ops = some o) :
    keyWrites o.ws ≤ sbTop b s ops := by
  by_cases hne : ops = []
  · subst hne
    rw [pe_keyWrites_nil hI hfill hw]
    exact Nat.zero_le _
  · exact pe_keyWrites_puts hb hI hfill hputs hne hw

end Contract.PE
