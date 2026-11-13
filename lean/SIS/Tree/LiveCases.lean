/-
`QLive`, the obligation that an operation keeps `LiveCounts` (bergdb 024-12,
TP7, `LiveCounts.lean`), for the operation cases.

* (1) A put into its leaf with room (`liveCase_putLeafRoom`). The leaf gets
  a key klong. Its live klongs are the ones before and the new one, so it has
  at least as many (`KNode.add_key_liveAt_length`). The tree reached is the
  one before, plus the new pointee, which is no node
  (`fReach_updN_leafPut`).
-/
import SIS.Tree.LiveCounts
import SIS.Tree.GetOpCases
import SIS.Tree.RangeOps

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! ## A key klong put into a leaf -/

/-- A key klong added at time t keeps every live klong at t but the one of its
compare value, which it replaces. -/
theorem KNode.add_key_liveAt_keep (n : KNode) (t : Time) (cv : Nat) (v : NodeId)
    (hw : klongsWf n.ks = true) (ht : ∀ s, Klong.time s ∈ n.ks → s ≤ t) (c : Nat) (y : NodeId)
    (hc : c ≠ cv) (h : (c, y) ∈ n.liveAt t) : (c, y) ∈ (n.add t (.key cv v)).liveAt t := by
  have ht' := KNode.add_times n t (.key cv v) (fun s h => by cases h) ht
  rw [KNode.liveAt_of_times _ t ht']
  rw [KNode.liveAt_of_times _ t ht] at h
  apply mem_of_lookup_nodup
  rw [KNode.add_key_live_lookup_of_wf n t cv c v hw]
  have hb : (cv == c) = false := by simpa using (Ne.symm hc)
  simp only [hb, Bool.false_eq_true, ↓reduceIte]
  exact lookup_of_mem_nodup _ (KNode.live_keys_nodup n) c y h

/-- A key klong added at time t leaves at least as many live klongs at t. -/
theorem KNode.add_key_liveAt_length (n : KNode) (t : Time) (cv : Nat) (v : NodeId)
    (hw : klongsWf n.ks = true) (ht : ∀ s, Klong.time s ∈ n.ks → s ≤ t) :
    (n.liveAt t).length ≤ ((n.add t (.key cv v)).liveAt t).length := by
  have ht' := KNode.add_times n t (.key cv v) (fun s h => by cases h) ht
  have hsub : ∀ c ∈ (n.liveAt t).map Prod.fst, c ∈ ((n.add t (.key cv v)).liveAt t).map Prod.fst := by
    intro c hc
    obtain ⟨⟨c', y⟩, hm, hcc⟩ := List.mem_map.mp hc
    simp only at hcc
    subst hcc
    by_cases hce : c' = cv
    · subst hce
      exact List.mem_map.mpr ⟨(c', v), KNode.add_key_liveAt_self n t c' v hw ht, rfl⟩
    · exact List.mem_map.mpr ⟨(c', y), KNode.add_key_liveAt_keep n t cv v hw ht c' y hce hm, rfl⟩
  have hnd : ((n.liveAt t).map Prod.fst).Nodup := by
    rw [KNode.liveAt_of_times _ t ht]; exact KNode.live_keys_nodup n
  have h := hnd.length_le_of_subset hsub
  simpa using h

/-- The tree reached after a key klong is put into a leaf L, with the flags, is
the tree before, but for the new pointee, which is no node. -/
theorem fReach_updN_leafPut (N : NodeId → Option KNode) (t : Time) (r L : NodeId) (n : KNode)
    (cv : Nat) (v : NodeId) (hL : N L = some n) (hnl : n.leaf = true)
    (hw : klongsWf n.ks = true) (ht : ∀ s, Klong.time s ∈ n.ks → s ≤ t) (hv : N v = none)
    (hvL : v ≠ L) :
    ∀ x b s, FReach (updN N L (n.add t (.key cv v))) t r x b s → FReach N t r x b s ∨ x = v := by
  intro x b s h
  induction h with
  | root => exact Or.inl FReach.root
  | inner x b s m c y _ hm hml hc ih =>
    rcases ih with ih | ih
    · by_cases hxL : x = L
      · subst hxL
        rw [updN_self] at hm
        cases hm
        rw [KNode.add_leaf, hnl] at hml
        cases hml
      · rw [updN_ne _ _ _ _ hxL] at hm
        exact Or.inl (FReach.inner x b s m c y ih hm hml hc)
    · subst ih
      rw [updN_ne _ _ _ _ hvL, hv] at hm
      cases hm
  | seg x b s m c y _ hm hml hc ih =>
    rcases ih with ih | ih
    · by_cases hxL : x = L
      · subst hxL
        rw [updN_self] at hm
        cases hm
        rcases KNode.add_key_liveAt_mem n t cv v hw ht c y hc with ⟨_, hy⟩ | ⟨_, hc'⟩
        · exact Or.inr hy
        · exact Or.inl (FReach.seg x b s n c y ih hL hnl hc')
      · rw [updN_ne _ _ _ _ hxL] at hm
        exact Or.inl (FReach.seg x b s m c y ih hm hml hc)
    · subst ih
      rw [updN_ne _ _ _ _ hvL, hv] at hm
      cases hm

/-- A key klong put into a leaf keeps `LiveCounts`. -/
theorem liveCounts_leafPut (p : Params) (N : NodeId → Option KNode) (t : Time) (r L : NodeId)
    (n : KNode) (cv : Nat) (v : NodeId) (hL : N L = some n) (hnl : n.leaf = true)
    (hw : klongsWf n.ks = true) (ht : ∀ s, Klong.time s ∈ n.ks → s ≤ t) (hv : N v = none)
    (hvL : v ≠ L) (hC : LiveCounts p N t r) :
    LiveCounts p (updN N L (n.add t (.key cv v))) t r := by
  intro x b s m hx hm
  rcases fReach_updN_leafPut N t r L n cv v hL hnl hw ht hv hvL x b s hx with hx' | hx'
  · by_cases hxL : x = L
    · subst hxL
      rw [updN_self] at hm
      cases hm
      obtain ⟨_, _, h3⟩ := hC x b s n hx' hL
      have hself := KNode.add_key_liveAt_self n t cv v hw ht
      have hlen := KNode.add_key_liveAt_length n t cv v hw ht
      refine ⟨fun hE => ?_, fun hl => ?_, fun hm hb => ?_⟩
      · rw [hE] at hself; cases hself
      · rw [KNode.add_leaf, hnl] at hl; cases hl
      · have := h3 hm hb; omega
    · rw [updN_ne _ _ _ _ hxL] at hm
      exact hC x b s m hx' hm
  · subst hx'
    rw [updN_ne _ _ _ _ hvL, hv] at hm
    cases hm

/-! ## (1) A put into its leaf with room -/

/-- (1), `LiveCounts`. -/
theorem liveCase_putLeafRoom (p : Params) (R : Struct BVal → Time → Prop) :
    OpCaseOK p R (QLive p) PutLeafRoomCase := by
  intro ts tx _ _ _ _ _ _ _ op _ _ _ w _ hI _ hP
  obtain ⟨pre, cv, h, L, n, hop, hK, hroom⟩ := hP
  subst hop
  obtain ⟨rk, hrk, _⟩ := keyLeaf_rk hK
  have ht : ∀ q ∈ fromVisits (wNode (ctxOf p ts).p (viewOf (treeRun p ts)) w) (ctxOf p ts).i
      (ctxOf p ts).p.fuel (pre ++ [cv]) w.top.rootKey, w.taken.contains q.1 = false := fun q hq =>
    hI.untaken q.1 (fromVisits_reach _ _ _ _ (fun x xn _ hn => hI.wf x xn hn) _ _ q.1 q.2
      ReachS.root hq)
  refine writerWP_mono (writerWP_put_room_after (ctxOf p ts) _ (viewCoherent_ctxOf p ts) pre cv h rk
    w hrk ht (keyLeaf_all hK hrk (fun m => m.size + 1 < (ctxOf p ts).p.M ∧
      deadOver (ctxOf p ts).p (m.add (ctxOf p ts).i (.key cv w.next)) = false) hroom)) ?_
  intro _ w' ⟨L', n', _, hn', hnl', _, h'top, hN'L, hN'⟩ _ hC
  rw [h'top]
  have hN'L2 : wNode p (viewOf (treeRun p ts)) w' L' =
      some (n'.add (ts.length + 1) (.key cv w.next)) := hN'L
  have hN'2 : ∀ x, x ≠ L' → wNode p (viewOf (treeRun p ts)) w' x =
      wNode p (viewOf (treeRun p ts)) w x := hN'
  have hfun : wNode p (viewOf (treeRun p ts)) w' =
      updN (wNode p (viewOf (treeRun p ts)) w) L' (n'.add (ts.length + 1) (.key cv w.next)) := by
    funext x
    by_cases hx : x = L'
    · subst hx; rw [hN'L2, updN_self]
    · rw [hN'2 x hx, updN_ne _ _ _ _ hx]
  rw [hfun]
  have hnone : wNode p (viewOf (treeRun p ts)) w w.next = none := hI.none_of_ge w.next (Nat.le_refl _)
  refine liveCounts_leafPut p _ _ _ L' n' cv w.next hn' hnl' (hI.wf L' n' hn') (hI.times L' n' hn')
    hnone (fun he => ?_) hC
  have hn'2 : wNode p (viewOf (treeRun p ts)) w L' = some n' := hn'
  rw [he, hn'2] at hnone
  cases hnone

end SIS.Tree
