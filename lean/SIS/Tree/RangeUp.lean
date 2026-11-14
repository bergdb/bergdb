import SIS.Tree.RangeNewSeg
import SIS.Tree.PutInvUp

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! The upward delete keeps the walk's ranges (bergdb 024-12, TP10;
`RangeOrder`): a node drops its klong to its child L, which is reached no more
(`rangeOrder_drop`); the upward delete that empties a segment's tree of one leaf,
stopping at the segment leaf above (`rangeOrder_del_up_segRoot`). -/

/-- The walk's ranges after the node s drops its live klong k1 to L, keeping
others only; L, reached no more, may change. -/
theorem rangeOrder_drop (N N' : NodeId → Option KNode) (t : Time) (r s L : NodeId) (sn sn' : KNode)
    (k1 : Nat) (hR : RangeOrder N t r) (hT : TreeOK N t r) (hs : N s = some sn)
    (hrs : TReach N t r s) (hk1 : (k1, L) ∈ sn.liveAt t) (hl' : sn'.leaf = sn.leaf)
    (hsub : ∀ c' z, (c', z) ∈ sn'.liveAt t → c' ≠ k1 ∧ (c', z) ∈ sn.liveAt t)
    (hN's : N' s = some sn') (hother : ∀ x, x ≠ s → x ≠ L → N' x = N x) : RangeOrder N' t r := by
  let N1 : NodeId → Option KNode := fun z => if z = s then some sn' else N z
  have hN1 : ∀ y, N1 y = if y = s then some sn' else N y := fun _ => rfl
  have hR1 : RangeOrder N1 t r :=
    rangeOrder_shrink N N1 t r s sn sn' hR hs hN1 hl' (fun c z h => (hsub c z h).2)
  -- L is reached no more
  have hsub1 : ∀ x c y, TLink N1 t x c y → TLink N t x c y := by
    intro x c y hl
    obtain ⟨m, hm, hc⟩ := hl
    by_cases hx : x = s
    · rw [hx] at hm ⊢
      simp only [N1, ↓reduceIte, Option.some.injEq] at hm
      subst hm
      exact ⟨sn, hs, (hsub c y hc).2⟩
    · simp only [N1, hx, ↓reduceIte] at hm
      exact ⟨m, hm, hc⟩
  have hLr : r ≠ L := fun h => hT.rootFree s k1 hrs ⟨sn, hs, h ▸ hk1⟩
  have hnoL : ¬ TReach N1 t r L := by
    intro h
    cases h with
    | root => exact hLr rfl
    | link hu hl =>
      rename_i u c
      have hu0 := tReach_of_sublinks _ _ t r hsub1 u hu
      obtain ⟨he, hc⟩ := hT.oneLink u c s k1 L hu0 hrs (hsub1 _ _ _ hl) ⟨sn, hs, hk1⟩
      subst he hc
      obtain ⟨m, hm, hcm⟩ := hl
      simp only [N1, ↓reduceIte, Option.some.injEq] at hm
      subst hm
      exact (hsub _ _ hcm).1 rfl
  refine rangeOrder_agree N1 N' t r hR1 ?_
  intro z hz
  have hzL : z ≠ L := fun h => hnoL (h ▸ hz)
  by_cases hzs : z = s
  · rw [hzs, hN's]; simp [N1]
  · rw [hother z hzs hzL]; simp [N1, hzs]

theorem rangeOrder_del_up_segRoot (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (pre0 : List Nat) (k1 cv : Nat) (rq L : NodeId) (n : KNode) (w : W)
    (hI : PutInv c base w) (hR : RangeOrder (wNode c.p base w) c.i w.top.rootKey)
    (hmerges : c.p.merges = false)
    (hrq : segRootR (wNode c.p base w) c.i c.p.fuel pre0 w.top.rootKey = some rq)
    (hL : getEqR (wNode c.p base w) c.i k1 c.p.fuel rq = some L)
    (hNL : wNode c.p base w L = some n) (hnl : n.leaf = true)
    (hne : bitsUnion n.lastBitmap (n.bitsOf cv) ≠ n.lastBitmap)
    (hempty : n.allKeysIn (bitsUnion n.lastBitmap (n.bitsOf cv)) = true)
    (hfirst : n.firstTime ≠ some c.i)
    (hseg : ∀ q qn, (q, k1) ∈ eqVisits (wNode c.p base w) c.i k1 c.p.fuel rq →
      wNode c.p base w q = some qn → qn.leaf = true →
      qn.allKeysIn (bitsUnion qn.lastBitmap (qn.bitsOf k1)) = false ∧
      bitsUnion qn.lastBitmap (qn.bitsOf k1) ≠ qn.lastBitmap ∧
      deadOver c.p (qn.setAt (qn.size - 1) (.del (bitsUnion qn.lastBitmap (qn.bitsOf k1)))) = false ∧
      deadOver c.p (qn.add c.i (.del (bitsUnion qn.lastBitmap (qn.bitsOf k1)))) = false ∧
      (lastIsDel qn.ks = false ∨ qn.lastTime ≠ some c.i → qn.size + 1 < c.p.M)) :
    WriterWP (putKv (.del (pre0 ++ [k1, cv]))) c w (fun _ w' =>
      RangeOrder (wNode c.p base w') c.i w'.top.rootKey) := by
  obtain ⟨_, _, ht, hrrq⟩ := segRoot_facts c base w hI pre0 k1 cv rq L n hrq hL hNL hnl
  apply writerWP_del_segRoot_leaf c base hvc pre0 k1 cv rq L n w hrq ht hI.ids.1 hI.ids.2.1 hL hNL hnl
    (fun q qn _ hqn => hI.wf q qn hqn)
  intro q qn d' w5 hqv hqn hql hk1 hlk5 hlq5 hsrc5 hr5 hpq' hpk _
  obtain ⟨hkeep, hqne, hd1, hd2, hroom⟩ := hseg q qn hqv hqn hql
  obtain ⟨pq, hpq⟩ : ∃ pq, w5.path[d']? = some (pq, q) := by
    cases h' : w5.path[d']? with
    | none => rw [h'] at hpq'; cases hpq'
    | some e => rw [h'] at hpq'; simp at hpq'; exact ⟨e.1, by rw [← hpq']⟩
  have hrq' : ReachS (wNode c.p base w) c.i w.top.rootKey q :=
    eqVisits_reach _ _ _ k1 c.p.fuel rq q k1 hrrq hqv
  have hLt : w.taken.contains L = false := (wNode_cases _ _ _ _ _ hNL).1
  have hqt : w.taken.contains q = false := (wNode_cases _ _ _ _ _ hqn).1
  have hqL : q ≠ L := by
    intro he; subst he
    exact hI.tree.no_self_link q k1 (reachS_tReach _ _ _ _ hrq') ⟨qn, hqn, hk1⟩
  simp only [writerWP_bind]
  unfold deleteUpward
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known L n c w5 hlk5]
  have hnb : (bitsUnion n.lastBitmap (n.bitsOf cv) == n.lastBitmap) = false := by simpa using hne
  simp only [hnb, Bool.false_eq_true, ↓reduceIte, hempty, Bool.not_true, writerWP_bind]
  refine writerWP_mono (writerWP_climb_stop d' L q pq k1 n qn c w5 hpk hpq hlk5 hlq5 hfirst hkeep) ?_
  rintro r v ⟨rfl, rfl⟩
  simp only [show (r == r + 1) = false by simp, Bool.false_eq_true, ↓reduceIte, note,
    writerWP_bind, writerWP_modify, writerWP_get]
  refine writerWP_mono (writerWP_foldlM_frame c base _ (fun b e w => ?_) _ 0 _) ?_
  · simp only [writerWP_bind]
    refine writerWP_mono (writerWP_getNode_frame3 e.2 c base hvc w) ?_
    intro _ u h
    simp only [writerWP_pure]
    exact h
  intro seg w6 ⟨hr6, hp6, hpa6⟩
  have hlk6 : w6.nodes.lookup L = some n := by
    obtain ⟨t, ht⟩ := hp6
    rw [← ht, List.lookup_append]
    simp only at hlk5 ⊢
    rw [hlk5]; rfl
  have hlq6 : w6.nodes.lookup q = some qn := by
    obtain ⟨t, ht⟩ := hp6
    rw [← ht, List.lookup_append]
    simp only at hlq5 ⊢
    rw [hlq5]; rfl
  simp only at hpa6
  rw [show r + 1 - r = 1 by omega, show List.range 1 = [0] from rfl]
  simp only [List.forIn_cons, List.forIn_nil, writerWP_bind, pathNode, writerWP_get, hpa6,
    Nat.sub_zero, hpk, writerWP_pure]
  rw [writerWP_getNode_known L n c w6 hlk6]
  have hf : (n.firstTime == some c.i) = false := by simpa using hfirst
  simp only [hf, Bool.false_eq_true, ↓reduceIte, writerWP_bind, writerWP_modify]
  refine writerWP_mono (writerWP_unlink_frame2 L n c _ hlk6) ?_
  intro _ w7 ⟨h7t, h7top, h7p, h7n, h7l⟩
  simp only at h7t h7top h7p h7n h7l
  have hlq7 : w7.nodes.lookup q = some qn := by rw [h7l q hqL]; exact hlq6
  simp only [writerWP_pure, h7p, hpa6, hpq, klongAt, writerWP_bind, writerWP_get]
  rw [hpk]
  simp only [writerWP_pure]
  rw [writerWP_getNode_known q qn c w7 hlq7]
  refine writerWP_ghOf_cached q qn c w7 hlq7 _ (fun gh => ?_)
  simp only [hql, ↓reduceIte, writerWP_bind, writerWP_modify]
  have htk7 : w7.taken = w.taken := by rw [h7t, hr6.2.2.1]; exact hr5.2.2.1
  have htop7 : w7.top = w.top := by rw [h7top, hr6.2.1]; exact hr5.2.1
  have hW7 : ∀ x, x ≠ L → wNode c.p base w7 x = wNode c.p base w x := by
    intro x hxL
    have h1 : wNode c.p base w7 x = wNode c.p base w6 x := by
      unfold wNode; rw [h7t, h7l x hxL]
    rw [h1, hr6.1]
    exact congrFun hr5.1 x
  have hqnt := hI.times q qn hqn
  refine writerWP_mono (writerWP_appendDeleteKlong_room_drop base q r k1 qn c _ hlq7
    (by simp only; rw [htk7]; exact hqt) hqnt hroom hd1 hd2 hqne) ?_
  intro _ w9 ⟨n', hl', ht', hsub, h9t, h9top, hN9⟩
  have hdrop : RangeOrder (wNode c.p base w9) c.i w9.top.rootKey := by
    rw [h9top, htop7]
    refine rangeOrder_drop (wNode c.p base w) _ c.i w.top.rootKey q L qn n' k1 hR hI.tree hqn
      (reachS_tReach _ _ _ _ hrq') hk1 hl' hsub (by rw [hN9]; simp) ?_
    intro x hxq hxL
    rw [hN9]
    simp only [hxq, ↓reduceIte]
    exact hW7 x hxL
  unfold afterDelete fresh
  simp only [writerWP_bind, writerWP_read, hmerges, Bool.false_eq_true, ↓reduceIte, writerWP_pure,
    Bool.not_false, writerWP_get, writerWP_set]
  exact hdrop

end SIS.Tree
