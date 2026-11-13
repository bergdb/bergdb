/-
The writer's tree kept by a put that splits the space root (bergdb 024-22,
`OpTreeOK`), on prover latest's writer states of GetRootSplit.lean: the space
split under a new root (`writerWP_put_rootSpaceSplit_tree`, from
`treeOK_rootSplit`).
-/
import SIS.Tree.WriterTreePut
import SIS.Tree.GetRootSplit

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- `writerWP_put_rootSpaceSplit` keeps the writer's tree, now from the new
root. The ids from the next one on are in neither the base nor a live klong of
the tree. -/
theorem writerWP_put_rootSpaceSplit_tree (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (cv h : Nat) (w : W) (n : KNode)
    (hroot : wNode c.p base w w.top.rootKey = some n) (hnl : n.leaf = true)
    (hrt : w.taken.contains w.top.rootKey = false)
    (hleaf : (∀ s, Klong.time s ∈ n.ks → s ≤ c.i) ∧
      c.p.M ≤ n.size + 1 ∧ n.firstTime ≠ some c.i ∧ c.p.splitAbove < (n.lastVersion c.i).size ∧
      n.live ≠ [])
    (hids : (∀ z, (w.nodes.lookup z).isSome = true → z < w.next) ∧
      (∀ z, (c.view z).isSome = true → z < w.next) ∧ (∀ z, w.taken.contains z = true → z < w.next) ∧
      w.top.rootKey < w.next)
    (hbaseF : ∀ z, w.next ≤ z → knodeOf c.p base z = none)
    (hT : TreeOK (wNode c.p base w) c.i w.top.rootKey)
    (hfreshT : ∀ z, w.next ≤ z → ∀ u c', TReach (wNode c.p base w) c.i w.top.rootKey u →
      ¬ TLink (wNode c.p base w) c.i u c' z) :
    WriterWP (putKv (.put [cv] h)) c w (fun _ w' =>
      TreeOK (wNode c.p base w') c.i w'.top.rootKey) := by
  obtain ⟨hidn, hidv, hidt, hidr⟩ := hids
  obtain ⟨htimes, hfull, hfirst, hsplit, hlive⟩ := hleaf
  unfold putKv pathClear findRoot pathAdd
  wpSimplify
  generalize hw2 : ({ ({ w with path := [] } : W) with
    path := ([] : List (Option Nat × NodeId)) ++ [(none, w.top.rootKey)] } : W) = w2
  have hr02 : ReadsAs c.p base w w2 := by subst hw2; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  have hw2n : w2.nodes = w.nodes := by subst hw2; rfl
  have hp2 : w2.path = [(none, w.top.rootKey)] := by subst hw2; rfl
  rw [putSegs.eq_2]
  unfold setValue
  wpSimplify
  have hfuel : 2 ≤ c.p.fuel := by unfold Params.fuel; omega
  have hev : eqVisits (wNode c.p base w2) c.i cv c.p.fuel w.top.rootKey = [(w.top.rootKey, cv)] := by
    obtain ⟨f2, hf2⟩ : ∃ f2, c.p.fuel = f2 + 1 := ⟨c.p.fuel - 1, by omega⟩
    rw [hf2, hr02.1]
    simp [eqVisits, hroot, hnl]
  have ht2 : ∀ q ∈ eqVisits (wNode c.p base w2) c.i cv c.p.fuel w.top.rootKey,
      w2.taken.contains q.1 = false := by
    rw [hev, hr02.2.2.1]
    intro q hq
    simp only [List.mem_singleton] at hq
    subst hq
    exact hrt
  refine writerWP_mono (writerWP_and
    (writerWP_descendLte_path cv c base hvc c.p.fuel w.top.rootKey w2 ht2 (by rw [hp2]; rfl))
    (writerWP_descendLte_cache cv c base hvc c.p.fuel w.top.rootKey w2 ht2)) ?_
  intro L w3 ⟨⟨hr23, n', hn', hnl', hlk3, hvisL, _, hdp⟩, ⟨_, hsrc3, _⟩⟩
  rw [hr02.1] at hn' hvisL
  have hr03 := ReadsAs.trans _ _ _ _ _ hr02 hr23
  have hnext3 : w3.next = w.next := hr03.2.2.2.2
  obtain ⟨hLr, hp3⟩ : L = w.top.rootKey ∧ w3.path = w2.path := by
    rcases hdp with h | ⟨pre', q, k1, qn, fd, _, _, hq, hql, _, _, _, hqv⟩
    · exact h
    · rw [hev] at hqv
      simp only [List.mem_singleton, Prod.mk.injEq] at hqv
      rw [hqv.1, hr02.1, hroot] at hq
      cases hq
      rw [hnl] at hql
      cases hql
  subst hLr
  rw [hroot] at hn'
  cases hn'
  unfold newValue fresh
  wpSimplify
  rw [writerWP_getNode_known _ n c _ (by simpa using hlk3)]
  have hcond : (decide (n.size + 1 < c.p.M) && !deadOver c.p (n.add c.i (.key cv w3.next))) = false := by
    have : ¬ n.size + 1 < c.p.M := by omega
    simp [this]
  simp only [hcond, Bool.false_eq_true, ↓reduceIte, pathSize, writerWP_bind, writerWP_get,
    writerWP_pure]
  have hlen : w3.path.length - 1 = 0 := by rw [hp3, hp2]; rfl
  rw [hlen]
  refine writerWP_mono (writerWP_appendKlongs_rootSpaceSplit w.top.rootKey n cv w3.next c _
    (by simpa using hlk3) hfirst hfull hsplit (by simp only; omega)) ?_
  intro _ wf hRS
  obtain ⟨hft, hftop, _, hfn⟩ := hRS
  simp only at hft hftop hfn
  rw [hr03.2.2.1] at hft
  rw [hnext3] at hfn hftop
  have hfree : ∀ z, w.next ≤ z → wNode c.p base w z = none := by
    intro z hz
    have htz : w.taken.contains z = false := by
      cases h' : w.taken.contains z with
      | false => rfl
      | true => have := hidt z h'; omega
    have hnz : w.nodes.lookup z = none := by
      cases h' : w.nodes.lookup z with
      | none => rfl
      | some _ => have := hidn z (by rw [h']; rfl); omega
    simp only [wNode, htz, Bool.false_eq_true, ↓reduceIte, hnz, hbaseF z hz]
  have htn : ∀ z, w.next ≤ z → wf.taken.contains z = false := by
    intro z hz
    rw [hft]
    cases h' : w.taken.contains z with
    | false => rfl
    | true => have := hidt z h'; omega
  rw [hftop]
  generalize hR : w.top.rootKey = x at *
  have hx1 : x ≠ w.next + 2 := by omega
  have hx2 : x ≠ w.next + 2 + 2 := by omega
  have hx3 : x ≠ w.next + 2 + 2 + 2 := by omega
  obtain ⟨r0, hr0'⟩ : ∃ r0, (n.live.drop (n.live.length / 2)).head? = some r0 := by
    cases hd : (n.live.drop (n.live.length / 2)).head? with
    | some r0 => exact ⟨r0, rfl⟩
    | none =>
      exfalso
      rw [List.head?_eq_none_iff, List.drop_eq_nil_iff] at hd
      have : n.live.length ≠ 0 := fun h0 => hlive (List.eq_nil_of_length_eq_zero h0)
      omega
  apply treeOK_rootSplit (wNode c.p base w) (wNode c.p base wf) c.i x (w.next + 2) (w.next + 2 + 2)
    (w.next + 2 + 2 + 2) w.next n cv r0 hT hroot hnl hr0' htimes
  · simp only [wNode, htn _ (by omega : w.next ≤ w.next + 2), Bool.false_eq_true, ↓reduceIte, hfn,
      Ne.symm hx1, hnl]
  · simp only [wNode, htn _ (by omega : w.next ≤ w.next + 2 + 2), Bool.false_eq_true, ↓reduceIte,
      hfn, Ne.symm hx2, show w.next + 2 + 2 ≠ w.next + 2 by omega, hnl]
  · simp only [wNode, htn _ (by omega : w.next ≤ w.next + 2 + 2 + 2), Bool.false_eq_true,
      ↓reduceIte, hfn, Ne.symm hx3, show w.next + 2 + 2 + 2 ≠ w.next + 2 by omega,
      show w.next + 2 + 2 + 2 ≠ w.next + 2 + 2 by omega, hnl]
    rfl
  · have hv : w.next ≠ x := by omega
    rw [← hr03.1]
    simp only [wNode, hft, hfn, hv, show w.next ≠ w.next + 2 by omega,
      show w.next ≠ w.next + 2 + 2 by omega, show w.next ≠ w.next + 2 + 2 + 2 by omega, ↓reduceIte,
      hr03.2.2.1]
  · intro z hzx hz1 hz2 hzR
    rw [← hr03.1]
    simp only [wNode, hft, hfn, hzx, hz1, hz2, hzR, ↓reduceIte, hr03.2.2.1]
  · exact hfree _ (by omega)
  · exact hfree _ (by omega)
  · exact hfree _ (by omega)
  · exact hfree _ (Nat.le_refl _)
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · intro z hz u c' hu
    exact hfreshT z (by omega) u c' hu
/-- The tree after a time split of the root x: a new root R holds x's last
version with the klong (cv, v) of a fresh v put; x is left behind. -/
theorem treeOK_rootTimeSplit (N N' : NodeId → Option KNode) (t : Time) (x R v : NodeId)
    (n l : KNode) (cv : Nat) (hT : TreeOK N t x) (hxn : N x = some n)
    (hnt : ∀ s, Klong.time s ∈ n.ks → s ≤ t)
    (hl_times : ∀ s, Klong.time s ∈ l.ks → s ≤ t)
    (hl_look : ∀ q', l.live.lookup q' = [(cv, v)].foldl (pairLookupStep q') (n.live.lookup q'))
    (hNR : N' R = some ⟨n.leaf, l.ks⟩) (hother : ∀ z, z ≠ x → z ≠ R → N' z = N z)
    (hfR : N R = none) (hvN : N v = none) (hvR : v ≠ R)
    (hfresh : ∀ z, (z = R ∨ z = v) → ∀ u c', TReach N t x u → ¬ TLink N t u c' z) :
    TreeOK N' t R := by
  have hxR : x ≠ R := fun h => by rw [h, hfR] at hxn; cases hxn
  have hxv : x ≠ v := fun h => by rw [h, hvN] at hxn; cases hxn
  have hRR : ¬ TReach N t x R := not_reach_fresh N t x R hT hfR (hfresh R (Or.inl rfl))
  have hvR' : ¬ TReach N t x v := not_reach_fresh N t x v hT hvN (hfresh v (Or.inr rfl))
  have hvN' : N' v = none := by rw [hother v (Ne.symm hxv) hvR]; exact hvN
  have hy_live : ∀ c' v', (c', v') ∈ ({ leaf := n.leaf, ks := l.ks } : KNode).liveAt t →
      (c' = cv ∧ v' = v) ∨ (c', v') ∈ n.liveAt t := by
    intro c' v' h
    rw [KNode.liveAt_of_times ({ leaf := n.leaf, ks := l.ks } : KNode) t hl_times] at h
    have hlk := lookup_of_mem_nodup _ (KNode.live_keys_nodup _) c' v' h
    have hlk' : l.live.lookup c' = some v' := by
      rw [← KNode.live_with_leaf l n.leaf]; exact hlk
    rw [hl_look c'] at hlk'
    simp only [List.foldl_cons, List.foldl_nil, pairLookupStep] at hlk'
    by_cases hcc : cv = c'
    · subst hcc; simp at hlk'; exact Or.inl ⟨rfl, hlk'.symm⟩
    · have hb : (cv == c') = false := by simpa using hcc
      rw [hb] at hlk'
      simp only [Bool.false_eq_true, ↓reduceIte] at hlk'
      right
      rw [KNode.liveAt_of_times n t hnt]
      exact mem_of_lookup_nodup _ c' v' hlk'
  apply treeOK_transfer_gone N N' t x R (fun z => z = R ∨ z = v) (fun z => z = x)
    (fun u c' => if u = x then (R, c') else (u, c')) hT
  · intro z hz
    rcases hz with hz | hz
    · rw [hz]; exact hRR
    · rw [hz]; exact hvR'
  · refine Or.inr ⟨Or.inl rfl, fun y c' hy hyg hl => ?_⟩
    obtain ⟨m, hm, hc⟩ := hl
    by_cases hyR : y = R
    · rw [hyR, hNR] at hm
      simp only [Option.some.injEq] at hm
      subst hm
      rcases hy_live c' R hc with ⟨_, h⟩ | hmem
      · exact hvR h.symm
      · exact hfresh R (Or.inl rfl) x c' TReach.root ⟨n, hxn, hmem⟩
    · have hyR' : TReach N t x y := by
        rcases hy with h | h
        · exact h
        · rcases h with h | h
          · exact absurd h hyR
          · rw [h, hvN'] at hm; cases hm
      rw [hother y hyg hyR] at hm
      exact hfresh R (Or.inl rfl) y c' hyR' ⟨m, hm, hc⟩
  · intro u c' z hu hug hl
    obtain ⟨m, hm, hc⟩ := hl
    by_cases huR : u = R
    · rw [huR, hNR] at hm
      simp only [Option.some.injEq] at hm
      subst hm
      rcases hy_live c' z hc with ⟨_, h⟩ | hmem
      · exact Or.inl (Or.inr h)
      · have hlk : TLink N t x c' z := ⟨n, hxn, hmem⟩
        refine Or.inr ⟨fun hzx => ?_, x, c', TReach.root, hlk, by simp [huR]⟩
        rw [hzx] at hlk
        exact hT.rootFree x c' TReach.root hlk
    · have huR' : TReach N t x u := by
        rcases hu with h | h
        · exact h
        · rcases h with h | h
          · exact absurd h huR
          · rw [h, hvN'] at hm; cases hm
      rw [hother u hug huR] at hm
      have hlk : TLink N t u c' z := ⟨m, hm, hc⟩
      refine Or.inr ⟨fun hzx => ?_, u, c', huR', hlk, by simp [hug]⟩
      rw [hzx] at hlk
      exact hT.rootFree u c' huR' hlk
  · intro u c' u' c'' z hu hug hu' hug' hz hl hl'
    have hone : ∀ y d, (TReach N t x y ∨ (y = R ∨ y = v)) → ¬ y = x → TLink N' t y d z →
        y = R ∧ d = cv := by
      intro y d hy hyg hl0
      obtain ⟨m, hm, hc⟩ := hl0
      by_cases hyR : y = R
      · rw [hyR, hNR] at hm
        simp only [Option.some.injEq] at hm
        subst hm
        rcases hy_live d z hc with ⟨hd, _⟩ | hmem
        · exact ⟨hyR, hd⟩
        · exact absurd ⟨n, hxn, hmem⟩ (hfresh z hz x d TReach.root)
      · have hyR' : TReach N t x y := by
          rcases hy with h | h
          · exact h
          · rcases h with h | h
            · exact absurd h hyR
            · rw [h, hvN'] at hm; cases hm
        rw [hother y hyg hyR] at hm
        exact absurd ⟨m, hm, hc⟩ (hfresh z hz y d hyR')
    obtain ⟨h1, h2⟩ := hone u c' hu hug hl
    obtain ⟨h3, h4⟩ := hone u' c'' hu' hug' hl'
    exact ⟨h1.trans h3.symm, h2.trans h4.symm⟩
  · intro z hz hzx
    rcases hz with hz | hz
    · exact hxR (hzx.symm.trans hz)
    · exact hxv (hzx.symm.trans hz)
  · rw [hNR]; exact ⟨_, rfl⟩

/-- What the tree from a new root above the root x reaches: the new root and
what x reached. -/
theorem tReach_newRootAbove (N N' : NodeId → Option KNode) (t : Time) (x R : NodeId) (m : KNode)
    (hT : TreeOK N t x) (hfR : N R = none)
    (hfresh : ∀ u c', TReach N t x u → ¬ TLink N t u c' R)
    (hNR : N' R = some m) (hm : ∀ c z, (c, z) ∈ m.liveAt t → c = 0 ∧ z = x)
    (hother : ∀ z, z ≠ R → N' z = N z) : ∀ y, TReach N' t R y → y = R ∨ TReach N t x y := by
  have hRR : ¬ TReach N t x R := not_reach_fresh N t x R hT hfR hfresh
  intro y hy
  induction hy with
  | root => exact Or.inl rfl
  | @link u c z _ hl ih =>
    obtain ⟨mm, hmm, hc⟩ := hl
    rcases ih with h | h
    · rw [h, hNR] at hmm
      simp only [Option.some.injEq] at hmm
      subst hmm
      rw [(hm c z hc).2]
      exact Or.inr TReach.root
    · have huR : u ≠ R := fun he => hRR (he ▸ h)
      rw [hother u huR] at hmm
      exact Or.inr (TReach.link h ⟨mm, hmm, hc⟩)

/-- A new root R above the root x, with x its only live child: the tree is
from R. -/
theorem treeOK_newRootAbove (N N' : NodeId → Option KNode) (t : Time) (x R : NodeId) (m : KNode)
    (hT : TreeOK N t x) (hfR : N R = none)
    (hfresh : ∀ u c', TReach N t x u → ¬ TLink N t u c' R)
    (hNR : N' R = some m) (hm : ∀ c z, (c, z) ∈ m.liveAt t → c = 0 ∧ z = x)
    (hother : ∀ z, z ≠ R → N' z = N z) : TreeOK N' t R := by
  have hRR : ¬ TReach N t x R := not_reach_fresh N t x R hT hfR hfresh
  have hb := tReach_newRootAbove N N' t x R m hT hfR hfresh hNR hm hother
  -- a link of N' from a reached node
  have hl' : ∀ y c z, (y = R ∨ TReach N t x y) → TLink N' t y c z →
      (y = R ∧ c = 0 ∧ z = x) ∨ (y ≠ R ∧ TLink N t y c z) := by
    intro y c z hy hl
    obtain ⟨mm, hmm, hc⟩ := hl
    by_cases hyR : y = R
    · rw [hyR, hNR] at hmm
      simp only [Option.some.injEq] at hmm
      subst hmm
      exact Or.inl ⟨hyR, hm c z hc⟩
    · rw [hother y hyR] at hmm
      exact Or.inr ⟨hyR, mm, hmm, hc⟩
  refine ⟨⟨m, hNR⟩, ?_, ?_⟩
  · intro y c hy hl
    rcases hl' y c R (hb y hy) hl with ⟨_, _, h⟩ | ⟨hyR, hlk⟩
    · obtain ⟨_, hk⟩ := hT.rootKey; rw [← h, hfR] at hk; cases hk
    · rcases hb y hy with h | h
      · exact hyR h
      · exact hfresh y c h hlk
  · intro y1 c1 y2 c2 z hy1 hy2 hl1 hl2
    rcases hl' y1 c1 z (hb y1 hy1) hl1 with ⟨h1, h1c, h1z⟩ | ⟨h1R, hlk1⟩ <;>
      rcases hl' y2 c2 z (hb y2 hy2) hl2 with ⟨h2, h2c, h2z⟩ | ⟨h2R, hlk2⟩
    · exact ⟨h1.trans h2.symm, h1c.trans h2c.symm⟩
    · have hy2' : TReach N t x y2 := (hb y2 hy2).resolve_left h2R
      rw [h1z] at hlk2
      exact absurd hlk2 (hT.rootFree y2 c2 hy2')
    · have hy1' : TReach N t x y1 := (hb y1 hy1).resolve_left h1R
      rw [h2z] at hlk1
      exact absurd hlk1 (hT.rootFree y1 c1 hy1')
    · exact hT.oneLink y1 c1 y2 c2 z ((hb y1 hy1).resolve_left h1R)
        ((hb y2 hy2).resolve_left h2R) hlk1 hlk2

/-- A put of a key of one segment into the space root, a leaf without room:
after the descent and the new value the writer appends the klong to the root
(`appendKlongs` at depth 0) from a state that reads as w, with the value at
w's next id. -/
theorem writerWP_put_root_append (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (cv h : Nat) (w : W) (n : KNode)
    (hroot : wNode c.p base w w.top.rootKey = some n) (hnl : n.leaf = true)
    (hrt : w.taken.contains w.top.rootKey = false)
    (hfull : ¬ (n.size + 1 < c.p.M ∧ deadOver c.p (n.add c.i (.key cv w.next)) = false))
    (hidn : ∀ z, (w.nodes.lookup z).isSome = true → z < w.next)
    (hidv : ∀ z, (c.view z).isSome = true → z < w.next)
    (post : Bool → W → Prop)
    (hk : ∀ w4 : W, w4.taken = w.taken → w4.top = w.top → w4.next = w.next + 2 →
      w4.vals = w.vals ++ [(w.next, h)] → w4.nodes.lookup w.top.rootKey = some n →
      (∀ z, (w4.nodes.lookup z).isSome = true → z < w.next) →
      wNode c.p base w4 = wNode c.p base w →
      WriterWP (appendKlongs 0 w.top.rootKey [(cv, w.next)]) c w4 (fun _ w' => post false w')) :
    WriterWP (putKv (.put [cv] h)) c w post := by
  have hfuel : 2 ≤ c.p.fuel := by unfold Params.fuel; omega
  unfold putKv pathClear findRoot pathAdd
  wpSimplify
  generalize hw2 : ({ ({ w with path := [] } : W) with
    path := ([] : List (Option Nat × NodeId)) ++ [(none, w.top.rootKey)] } : W) = w2
  have hr02 : ReadsAs c.p base w w2 := by subst hw2; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  have hw2n : w2.nodes = w.nodes := by subst hw2; rfl
  have hp2 : w2.path = [(none, w.top.rootKey)] := by subst hw2; rfl
  rw [putSegs.eq_2]
  unfold setValue
  wpSimplify
  have hev : eqVisits (wNode c.p base w2) c.i cv c.p.fuel w.top.rootKey = [(w.top.rootKey, cv)] := by
    obtain ⟨f2, hf2⟩ : ∃ f2, c.p.fuel = f2 + 1 := ⟨c.p.fuel - 1, by omega⟩
    rw [hf2, hr02.1]
    simp [eqVisits, hroot, hnl]
  have ht2 : ∀ q ∈ eqVisits (wNode c.p base w2) c.i cv c.p.fuel w.top.rootKey,
      w2.taken.contains q.1 = false := by
    rw [hev, hr02.2.2.1]
    intro q hq
    simp only [List.mem_singleton] at hq
    subst hq
    exact hrt
  refine writerWP_mono (writerWP_and
    (writerWP_descendLte_path cv c base hvc c.p.fuel w.top.rootKey w2 ht2 (by rw [hp2]; rfl))
    (writerWP_descendLte_cache cv c base hvc c.p.fuel w.top.rootKey w2 ht2)) ?_
  intro L w3 ⟨⟨hr23, n', hn', hnl', hlk3, hvisL, _, hdp⟩, ⟨_, hsrc3, _⟩⟩
  rw [hr02.1] at hn' hvisL
  have hr03 := ReadsAs.trans _ _ _ _ _ hr02 hr23
  have hnext3 : w3.next = w.next := hr03.2.2.2.2
  obtain ⟨hLr, hp3⟩ : L = w.top.rootKey ∧ w3.path = w2.path := by
    rcases hdp with h | ⟨pre', q, k1, qn, fd, _, _, hq, hql, _, _, _, hqv⟩
    · exact h
    · rw [hev] at hqv
      simp only [List.mem_singleton, Prod.mk.injEq] at hqv
      rw [hqv.1, hr02.1, hroot] at hq
      cases hq
      rw [hnl] at hql
      cases hql
  subst hLr
  rw [hroot] at hn'
  cases hn'
  unfold newValue fresh
  wpSimplify
  rw [writerWP_getNode_known _ n c _ (by simpa using hlk3)]
  have hcond : (decide (n.size + 1 < c.p.M) && !deadOver c.p (n.add c.i (.key cv w3.next))) = false := by
    rw [hnext3]
    cases hd : deadOver c.p (n.add c.i (.key cv w.next)) with
    | true => simp
    | false =>
      have : ¬ n.size + 1 < c.p.M := fun hlt => hfull ⟨hlt, hd⟩
      simp [this]
  simp only [hcond, Bool.false_eq_true, ↓reduceIte, pathSize, writerWP_bind, writerWP_get,
    writerWP_pure]
  have hsrcw3 : ∀ z, (w3.nodes.lookup z).isSome = true → z < w.next := by
    intro z hz
    rcases hsrc3 z hz with h1 | h1
    · rw [hw2n] at h1; exact hidn z h1
    · exact hidv z h1
  have hlen : w3.path.length - 1 = 0 := by rw [hp3, hp2]; rfl
  rw [hlen, hnext3]
  apply hk
  · exact hr03.2.2.1
  · exact hr03.2.1
  · simp
  · simp [hr03.2.2.2.1]
  · simpa using hlk3
  · exact hsrcw3
  · rw [← hr03.1]; rfl

/-- `writerWP_put_rootTimeSplit` keeps the writer's tree, now from the new root
(the root's last version with the put). -/
theorem writerWP_put_rootTimeSplit_tree (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (cv h : Nat) (w : W) (n : KNode)
    (hroot : wNode c.p base w w.top.rootKey = some n) (hnl : n.leaf = true)
    (hrt : w.taken.contains w.top.rootKey = false)
    (hleaf : (∀ s, Klong.time s ∈ n.ks → s ≤ c.i) ∧
      ¬ (n.size + 1 < c.p.M ∧ deadOver c.p (n.add c.i (.key cv w.next)) = false) ∧
      n.firstTime ≠ some c.i ∧ (c.p.M ≤ n.size + 1 → (n.lastVersion c.i).size ≤ c.p.splitAbove))
    (hids : (∀ z, (w.nodes.lookup z).isSome = true → z < w.next) ∧
      (∀ z, (c.view z).isSome = true → z < w.next) ∧ (∀ z, w.taken.contains z = true → z < w.next) ∧
      w.top.rootKey < w.next)
    (hbaseF : ∀ z, w.next ≤ z → knodeOf c.p base z = none)
    (hT : TreeOK (wNode c.p base w) c.i w.top.rootKey)
    (hfreshT : ∀ z, w.next ≤ z → ∀ u c', TReach (wNode c.p base w) c.i w.top.rootKey u →
      ¬ TLink (wNode c.p base w) c.i u c' z) :
    WriterWP (putKv (.put [cv] h)) c w (fun _ w' =>
      TreeOK (wNode c.p base w') c.i w'.top.rootKey) := by
  obtain ⟨hidn, hidv, hidt, hidr⟩ := hids
  obtain ⟨htimes, hfull, hfirst, hsplit⟩ := hleaf
  have hfree : ∀ z, w.next ≤ z → wNode c.p base w z = none := by
    intro z hz
    have htz : w.taken.contains z = false := by
      cases h' : w.taken.contains z with
      | false => rfl
      | true => have := hidt z h'; omega
    have hnz : w.nodes.lookup z = none := by
      cases h' : w.nodes.lookup z with
      | none => rfl
      | some _ => have := hidn z (by rw [h']; rfl); omega
    simp only [wNode, htz, Bool.false_eq_true, ↓reduceIte, hnz, hbaseF z hz]
  apply writerWP_put_root_append c base hvc cv h w n hroot hnl hrt hfull hidn hidv
  intro w4 h4t h4top h4next _ h4lk h4src hW4
  have hny : w4.nodes.lookup w4.next = none := by
    cases h' : w4.nodes.lookup w4.next with
    | none => rfl
    | some _ => have := h4src _ (by rw [h']; rfl); omega
  refine writerWP_mono (writerWP_appendKlongs_rootTimeSplit w.top.rootKey n cv w.next c w4 h4lk
    hfirst hfull hsplit (by omega) hny) ?_
  intro _ wf ⟨l, _, _, hl_times, hl_look, hft, hftop, _, hfn⟩
  rw [h4next] at hftop hfn
  rw [hftop]
  have hft' : wf.taken = w.taken := hft.trans h4t
  have htn : w.taken.contains (w.next + 2) = false := by
    cases h' : w.taken.contains (w.next + 2) with
    | false => rfl
    | true => have := hidt _ h'; omega
  apply treeOK_rootTimeSplit (wNode c.p base w) (wNode c.p base wf) c.i w.top.rootKey (w.next + 2)
    w.next n l cv hT hroot htimes hl_times hl_look
  · simp only [wNode, hft', htn, Bool.false_eq_true, ↓reduceIte, hfn,
      show w.next + 2 ≠ w.top.rootKey by omega]
  · intro z hzx hzR
    rw [← hW4]
    simp only [wNode, hft', hfn, hzx, hzR, ↓reduceIte, h4t]
  · exact hfree _ (by omega)
  · exact hfree _ (Nat.le_refl _)
  · omega
  · intro z hz u c' hu
    rcases hz with hz | hz <;> rw [hz] <;> exact hfreshT _ (by omega) u c' hu

/-- `writerWP_put_rootSpaceSplitInPlace` keeps the writer's tree, now from the
new root above the root, which holds the first half. -/
theorem writerWP_put_rootSpaceSplitInPlace_tree (c : Ctx) (base : View BVal)
    (hvc : ViewCoherent c base) (cv h : Nat) (w : W) (n : KNode)
    (hroot : wNode c.p base w w.top.rootKey = some n) (hnl : n.leaf = true)
    (hrt : w.taken.contains w.top.rootKey = false)
    (hleaf : (∀ s, Klong.time s ∈ n.ks → s ≤ c.i) ∧
      c.p.M ≤ n.size + 1 ∧ n.firstTime = some c.i ∧ c.p.splitAbove < (n.lastVersion c.i).size ∧
      n.live ≠ [])
    (hids : (∀ z, (w.nodes.lookup z).isSome = true → z < w.next) ∧
      (∀ z, (c.view z).isSome = true → z < w.next) ∧ (∀ z, w.taken.contains z = true → z < w.next) ∧
      w.top.rootKey < w.next)
    (hbaseF : ∀ z, w.next ≤ z → knodeOf c.p base z = none)
    (hT : TreeOK (wNode c.p base w) c.i w.top.rootKey)
    (hfreshT : ∀ z, w.next ≤ z → ∀ u c', TReach (wNode c.p base w) c.i w.top.rootKey u →
      ¬ TLink (wNode c.p base w) c.i u c' z) :
    WriterWP (putKv (.put [cv] h)) c w (fun _ w' =>
      TreeOK (wNode c.p base w') c.i w'.top.rootKey) := by
  obtain ⟨hidn, hidv, hidt, hidr⟩ := hids
  obtain ⟨htimes, hfull, hfirst, hsplit, hlive⟩ := hleaf
  have hfree : ∀ z, w.next ≤ z → wNode c.p base w z = none := by
    intro z hz
    have htz : w.taken.contains z = false := by
      cases h' : w.taken.contains z with
      | false => rfl
      | true => have := hidt z h'; omega
    have hnz : w.nodes.lookup z = none := by
      cases h' : w.nodes.lookup z with
      | none => rfl
      | some _ => have := hidn z (by rw [h']; rfl); omega
    simp only [wNode, htz, Bool.false_eq_true, ↓reduceIte, hnz, hbaseF z hz]
  have hntk : ∀ z, w.next ≤ z → w.taken.contains z = false := by
    intro z hz
    cases h' : w.taken.contains z with
    | false => rfl
    | true => have := hidt z h'; omega
  apply writerWP_put_root_append c base hvc cv h w n hroot hnl hrt (fun hh => by omega) hidn hidv
  intro w4 h4t h4top h4next _ h4lk h4src hW4
  have hny : w4.nodes.lookup (w4.next + 2) = none := by
    cases h' : w4.nodes.lookup (w4.next + 2) with
    | none => rfl
    | some _ => have := h4src _ (by rw [h']; rfl); omega
  refine writerWP_mono (writerWP_appendKlongs_rootSpaceSplitInPlace w.top.rootKey n cv w.next c w4
    h4lk hfirst hfull hsplit (by omega) hny) ?_
  intro _ wf hA
  obtain ⟨hft, hftop, hfv, hfn⟩ := hA
  generalize hR : w.top.rootKey = x at *
  -- a writer state with the new root above x and its only klong
  let qn : KNode := ⟨false, newKlongs c.i [(0, x)]⟩
  let w1 : W := { w4 with nodes := upsert w4.nodes (w4.next + 2) qn, top := wf.top }
  have hxR : x ≠ w4.next + 2 := by omega
  have hW1 : ∀ z, z ≠ w4.next + 2 → wNode c.p base w1 z = wNode c.p base w z := by
    intro z hz
    rw [← hW4]
    simp only [w1, wNode, lookup_upsert, hz, ↓reduceIte]
  have hW1R : wNode c.p base w1 (w4.next + 2) = some qn := by
    simp only [w1, wNode, h4t, hntk _ (by omega : w.next ≤ w4.next + 2), Bool.false_eq_true,
      ↓reduceIte, lookup_upsert]
  have hqt : ∀ s, Klong.time s ∈ qn.ks → s ≤ c.i := newKlongs_times c.i _
  have hqlive : ∀ c' z, (c', z) ∈ qn.liveAt c.i → c' = 0 ∧ z = x := by
    intro c' z hm
    have := liveAt_newKlongs_mem false c.i c.i [(0, x)] c' z hm
    simpa using this
  have hqk : (0, x) ∈ qn.liveAt c.i := by
    rw [KNode.liveAt_of_times qn c.i hqt]
    apply mem_of_lookup_nodup
    rw [KNode.newKlongs_live_lookup false c.i [(0, x)] (by simp) 0]
    simp
  have hT1 : TreeOK (wNode c.p base w1) c.i w1.top.rootKey := by
    show TreeOK (wNode c.p base w1) c.i wf.top.rootKey
    rw [hftop]
    apply treeOK_newRootAbove (wNode c.p base w) (wNode c.p base w1) c.i x (w4.next + 2) qn hT
      (hfree _ (by omega)) (fun u c' hu => hfreshT _ (by omega) u c' hu) hW1R hqlive hW1
  have h1top : w1.top.rootKey = w4.next + 2 := hftop
  have h1next : w1.next = w4.next := rfl
  obtain ⟨r0, hr0'⟩ : ∃ r0, (n.live.drop (n.live.length / 2)).head? = some r0 := by
    cases hd : (n.live.drop (n.live.length / 2)).head? with
    | some r0 => exact ⟨r0, rfl⟩
    | none =>
      exfalso
      rw [List.head?_eq_none_iff, List.drop_eq_nil_iff] at hd
      have : n.live.length ≠ 0 := fun h0 => hlive (List.eq_nil_of_length_eq_zero h0)
      omega
  have hb1 := tReach_newRootAbove (wNode c.p base w) (wNode c.p base w1) c.i x (w4.next + 2) qn hT
    (hfree _ (by omega)) (fun u c' hu => hfreshT _ (by omega) u c' hu) hW1R hqlive hW1
  apply treeOK_inPlaceSplitAfter c.p base c w1 wf x (w4.next + 2) n qn 0 cv w.next r0 rfl hT1
  · refine ⟨hft, rfl, hfv, ?_⟩
    intro z
    rw [hfn z]
    by_cases hzx : z = x
    · simp [hzx]
    · simp only [hzx, ↓reduceIte]
      by_cases hz2 : z = w4.next + 2
      · subst hz2
        simp only [show w4.next + 2 ≠ w4.next by omega, ↓reduceIte, w1]
        show _ = some (KNode.add ⟨false, newKlongs c.i [(0, x)]⟩ c.i _)
        rw [KNode.newKlongs_add_key]
        rfl
      · simp only [hz2, ↓reduceIte, w1, lookup_upsert]
  · rw [hW1 x hxR]; exact hroot
  · exact hW1R
  · exact hxR.symm
  · exact hqk
  · rw [h1top]; exact TReach.root
  · exact hnl
  · exact hr0'
  · exact htimes
  · exact hqt
  · exact klongsWf_newKlongs c.i _
  · rw [h1next, hW1 _ (by omega)]; exact hfree _ (by omega)
  · rw [hW1 _ (by omega)]; exact hfree _ (Nat.le_refl _)
  · simp only [w1, h4t]; exact hntk _ (by omega)
  · rw [h1next]; omega
  · intro z hz u c' hu hl
    have hzw : w.next ≤ z := by rw [h1next] at hz; omega
    rw [h1top] at hu
    rcases hb1 u hu with hu' | hu'
    · obtain ⟨mm, hmm, hc⟩ := hl
      rw [hu', hW1R] at hmm
      simp only [Option.some.injEq] at hmm
      subst hmm
      have := (hqlive c' z hc).2
      omega
    · have huR : u ≠ w4.next + 2 := by
        intro he
        rw [he] at hu'
        exact not_reach_fresh _ _ _ _ hT (hfree _ (by omega))
          (fun u c' hu => hfreshT _ (by omega) u c' hu) hu'
      obtain ⟨mm, hmm, hc⟩ := hl
      rw [hW1 u huR] at hmm
      exact hfreshT z hzw u c' hu' ⟨mm, hmm, hc⟩

end SIS.Tree
