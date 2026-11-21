/-
bergdb 030-37: the inner-loop potential comes from counted deletes.
A remaining small leaf is alone after rebalance. Its filled parent lost
at least one other child, so the small parent and the small leaf have
separate delete allowances, including at node size 8 (m = 2).
-/
import Contract.Proof.DnbInnerBudget

namespace Contract.PE

open DNB PeProof

variable {i : Time} {s : Tree}

theorem innerPotential_old {cf : Cfg} {y : NodeId} {n : KNode}
    (hk : getKey s y = some n) : innerPotential cf s (.old y) = 0 := by
  simp [innerPotential, openEs, hk, smallLeaf, VN.changed, smallLeaves, List.filter_map]

theorem old_inner_leaf_resources {b G H : Nat} (hb : 8 ≤ b) (hks : KsOk b s)
    {g y : Nat} (hs : Shaped (Cfg.java b G H) s g 1 y)
    (hf : Filled (Cfg.java b G H) s false y) :
    ∃ n, getKey s y = some n ∧ n.ks.length ≤ b ∧
      (Cfg.java b G H).m ≤ (live n.ks).length ∧
      LeafReady b G H i s ((live n.ks).map (fun q => (q.1, VN.old q.2))) := by
  obtain ⟨n, hobj, hk, _, hl, _, _⟩ := shaped_getKey hs
  have hnleaf : n.leaf = false := by simpa using hl
  obtain ⟨_, hkids⟩ := shaped_inner hs hobj
  have hfn := filled_key hf hobj
  have hm2 := (java_params (G := G) (H := H) hb).1
  refine ⟨n, hk, (hks y n hobj).2, hfn.2.1 hm2 rfl, ?_, ?_, ?_⟩
  · intro e he
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp he
    obtain ⟨m, hm, hmk, _, _, _, _⟩ := shaped_getKey (hkids q.1 q.2 hq)
    have hfill := (filled_key (hfn.2.2.2 q.1 q.2 hq hnleaf) hm).2.1 hm2 rfl
    exact JoinLeaf.old hmk (hks q.2 m hm).2 hfill
  · intro e he
    obtain ⟨q, _, rfl⟩ := List.mem_map.mp he
    rfl
  · right
    unfold findSmall
    rw [Option.map_eq_none_iff, List.find?_eq_none]
    intro p hp
    have he := List.mem_of_getElem? (mem_zipIdx_get hp).2
    obtain ⟨q, _, hq⟩ := List.mem_map.mp he
    have hv : p.1.2 = VN.old q.2 := congrArg Prod.snd hq.symm
    simp [hv, VN.changed]

theorem planned_inner_leaf_resources {b G H : Nat} (hb : 8 ≤ b) {f g y nd : Nat}
    {n : KNode} {es es2 : List (Nat × VN)} {v : VN} {acc acc' : Acc} {r : SR}
    (hk : getKey s y = some n) (hks : n.ks.length ≤ b)
    (hfill : (Cfg.java b G H).m ≤ (live n.ks).length)
    (hv : ∀ e ∈ es, JoinLeaf b G H i s e.2)
    (hbudget : (live n.ks).length + smallLeaves (Cfg.java b G H) (kept es) ≤ (kept es).length + nd)
    (hr : rebalance (Cfg.java b G H) i s f g 0 es = some es2)
    (hm : mkNode (Cfg.java b G H) i s (some y) g 1 false es2 = some v)
    (hp : PlanSpecD b s g 1 y false v acc acc' r) (hnd : r.nd = nd) :
    JoinInner b G H i s v ∧ (v.isEmpty = true → 1 ≤ nd) ∧
      innerPotential (Cfg.java b G H) s v ≤ nd := by
  have hmerges := (java_params (G := G) (H := H) hb).2.2.2.2.2.2
  have hm2 := (java_params (G := G) (H := H) hb).1
  have hkv : ∀ e ∈ kept es, JoinLeaf b G H i s e.2 :=
    fun e he => hv e (List.mem_of_mem_filter he)
  have hkne : ∀ e ∈ kept es, e.2.isEmpty = false := by
    intro e he
    have := (List.mem_filter.mp he).2
    simpa using this
  have hrl : LeafReady b G H i s es2 ∧
      (live n.ks).length + smallLeaves (Cfg.java b G H) es2 ≤ es2.length + nd := by
    cases f with
    | zero => simp [rebalance] at hr
    | succ f =>
      have hr' := hr
      change (if !(Cfg.java b G H).merges then some (kept es) else
        joinLoop (Cfg.java b G H) i s g 0 (fun J => rebalance (Cfg.java b G H) i s f g (0 - 1) J)
          ((kept es).length + 1) (kept es)) = some es2 at hr'
      simp only [hmerges, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hr'
      obtain ⟨j, hv2, _, _, hlen, hsmall, _, _, _⟩ := joinLoop_leaf_account hb _ _ _ hkv hr'
      obtain ⟨_, _, hne2⟩ := joinLoop_leaf_extra hb _ _ _ hkv hkne hr'
      exact ⟨⟨hv2, hne2, rebalance_exit hr hmerges⟩, by omega⟩
  have hform : v = .node (some y) g 1 false (renameHead 0 es2) (renameHead 0 (entries es2))
      (decideNode (Cfg.java b G H) i (some n) false (renameHead 0 (entries es2))) := by
    unfold mkNode at hm
    simp only [Nat.one_ne_zero, beq_iff_eq, ↓reduceIte, hk] at hm
    change some (.node (some y) g 1 false (renameHead 0 es2)
      (renameHead 0 (entries (renameHead 0 es2)))
      (decideNode (Cfg.java b G H) i (some n) false
        (renameHead 0 (entries (renameHead 0 es2))))) = some v at hm
    rw [entries_renameHead, renameHead_renameHead] at hm
    exact (Option.some.inj hm).symm
  rw [hform] at hp ⊢
  obtain ⟨n', es', F, d, hk', heq, _, hloss, hgrow⟩ := hp.shape
  change getKey s y = some n' at hk'
  rw [hk] at hk'; cases hk'
  cases heq
  have hFL : (renameHead 0 (entries es2)).length = (entries es2).length := renameHead_length _ _
  have hReady := leafReady_rename hrl.1 0
  have hJI : JoinInner b G H i s (.node (some y) g 1 false (renameHead 0 es2)
      (renameHead 0 (entries es2))
      (decideNode (Cfg.java b G H) i (some n) false (renameHead 0 (entries es2)))) := by
    have hsame : decideNode (Cfg.java b G H) i (some n) false (renameHead 0 (entries es2)) = .same →
        (Cfg.java b G H).m ≤ (renameHead 0 (entries es2)).length := by
      intro hs
      have he := dec_same hs
      have hlen := congrArg List.length he
      rw [List.length_map] at hlen
      omega
    simpa only [entries_renameHead, renameHead_renameHead] using
      (JoinInner.planned (y := y) (g := g) hks hReady
        (by simpa only [entries_renameHead, renameHead_renameHead] using hgrow)
        (by simpa only [entries_renameHead, renameHead_renameHead] using hsame))
  refine ⟨hJI, ?_, ?_⟩
  · intro he
    simp only [VN.isEmpty, List.isEmpty_iff] at he
    rw [he, List.length_nil, hnd] at hloss
    omega
  · have hpot : innerPotential (Cfg.java b G H) s (.node (some y) g 1 false (renameHead 0 es2)
        (renameHead 0 (entries es2))
        (decideNode (Cfg.java b G H) i (some n) false (renameHead 0 (entries es2)))) =
        (if smallLeaf (Cfg.java b G H) (.node (some y) g 1 false (renameHead 0 es2)
          (renameHead 0 (entries es2))
          (decideNode (Cfg.java b G H) i (some n) false (renameHead 0 (entries es2)))) then 1 else 0) +
          smallLeaves (Cfg.java b G H) es2 := by
      simp only [innerPotential, openEs, Option.getD_some, smallLeaves_rename]
    rw [hpot]
    have hsmall := leafReady_small hb hrl.1
    by_cases hs : 0 < smallLeaves (Cfg.java b G H) es2
    · have hlen := (hsmall.2 hs).1
      have hres := hrl.2
      split <;> omega
    · have hzero : smallLeaves (Cfg.java b G H) es2 = 0 := by omega
      rw [hzero, Nat.add_zero]
      split
      · rename_i hs
        have hsize := hJI.small.mp hs
        change (renameHead 0 (entries es2)).length < (Cfg.java b G H).m at hsize
        rw [hnd] at hloss
        omega
      · omega

end Contract.PE
