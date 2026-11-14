import SIS.Tree.RangeRun

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! The walk's ranges kept by the operations that change one node (bergdb
024-12, TP10; `RangeOrder`): a put into a leaf with room, a delete with no live
klong, a delete's bitmap in a leaf with room. -/

/-- The walk's ranges after one node x loses live klongs only. -/
theorem rangeOrder_shrink (N N' : NodeId → Option KNode) (t : Time) (r x : NodeId) (n n' : KNode)
    (hR : RangeOrder N t r) (hn : N x = some n)
    (hN' : ∀ y, N' y = if y = x then some n' else N y) (hl : n'.leaf = n.leaf)
    (hsub : ∀ c z, (c, z) ∈ n'.liveAt t → (c, z) ∈ n.liveAt t) : RangeOrder N' t r := by
  apply rangeOrder_nodeChange N N' t r x n n' hR hn (by rw [hN']; simp) hl
    (fun z hz => by rw [hN']; simp [hz])
  · intro lo hi hx
    exact nodeRange_sub n n' t lo lo hi hi (hR x lo hi n hx hn) hl
      (fun q hq => ⟨q, hsub q.1 q.2 hq, rfl⟩) (Nat.le_refl _) (HiLE.refl _)
  · intro c z hz; exact Or.inl (hsub c z hz)
  · intro _ c z _ _ r' hr' hlt; exact ⟨r', hsub r'.1 r'.2 hr', hlt, Nat.le_refl _⟩

/-- A put into the leaf of a key's last segment with room keeps the walk's
ranges. -/
theorem rangeOrder_put_room (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (pre : List Nat) (cv h : Nat) (rk : NodeId) (w : W) (hI : PutInv c base w)
    (hR : RangeOrder (wNode c.p base w) c.i w.top.rootKey)
    (hrk : segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk)
    (hroom : ∀ L n, (L, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      wNode c.p base w L = some n → n.leaf = true →
      n.size + 1 < c.p.M ∧ deadOver c.p (n.add c.i (.key cv w.next)) = false) :
    WriterWP (putKv (.put (pre ++ [cv]) h)) c w (fun _ w' =>
      RangeOrder (wNode c.p base w') c.i w'.top.rootKey) := by
  have ht : ∀ q ∈ fromVisits (wNode c.p base w) c.i c.p.fuel (pre ++ [cv]) w.top.rootKey,
      w.taken.contains q.1 = false := fun q hq =>
    hI.untaken q.1 (fromVisits_reach _ _ _ _ (fun x xn _ hn => hI.wf x xn hn) _ _ q.1 q.2
      ReachS.root hq)
  refine writerWP_mono (writerWP_put_room_after c base hvc pre cv h rk w hrk ht hroom) ?_
  intro _ w' ⟨L, n, hL, hn, hnl, _, h'top, hN'L, hN'⟩
  rw [h'top]
  have hfun : wNode c.p base w' = updN (wNode c.p base w) L (n.add c.i (.key cv w.next)) := by
    funext x
    by_cases hx : x = L
    · subst hx; rw [hN'L, updN_self]
    · rw [hN' x hx, updN_ne _ _ _ _ hx]
  rw [hfun]
  exact rangeOrder_leafPut (wNode c.p base w) c.i w.top.rootKey hR hI.tree hI.wf hI.times c.p.fuel
    pre cv rk L w.next n hrk hL hn hnl (hI.none_of_ge w.next (Nat.le_refl _))

/-- `putInv_del_noop_seg` for the walk's ranges: a delete of a key with no live klong. -/
theorem rangeOrder_del_noop_seg (c : Ctx) (base : View BVal)
    (hvc : ViewCoherent c base) (pre : List Nat) (cv : Nat) (rk : NodeId) (w : W)
    (hI : PutInv c base w) (hR : RangeOrder (wNode c.p base w) c.i w.top.rootKey)
    (hrk : segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk)
    (hleaf : ∀ L n, (L, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      wNode c.p base w L = some n → n.leaf = true →
      bitsUnion n.lastBitmap (n.bitsOf cv) = n.lastBitmap) :
    WriterWP (putKv (.del (pre ++ [cv]))) c w (fun _ w' =>
      RangeOrder (wNode c.p base w') c.i w'.top.rootKey) := by
  have ht : ∀ q ∈ fromVisits (wNode c.p base w) c.i c.p.fuel (pre ++ [cv]) w.top.rootKey,
      w.taken.contains q.1 = false := fun q hq =>
    hI.untaken q.1 (fromVisits_reach _ _ _ _ (fun x xn _ hn => hI.wf x xn hn) _ _ q.1 q.2
      ReachS.root hq)
  unfold putKv pathClear findRoot pathAdd
  wpSimplify
  generalize hw2 : ({ ({ w with path := [] } : W) with
    path := ([] : List (Option Nat × NodeId)) ++ [(none, w.top.rootKey)] } : W) = w2
  have hr02 : ReadsAs c.p base w w2 := by subst hw2; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  refine writerWP_putSegs_prefix c base hvc (pre ++ [cv]) none cv _ pre w.top.rootKey rk w2
    (by rw [hr02.1, hr02.2.2.1]; exact ht) (by rw [hr02.1]; exact hrk) ?_
  intro w2' hr2'
  have hr0 := ReadsAs.trans _ _ _ _ _ hr02 hr2'
  unfold setValue
  wpSimplify
  have ht2 : ∀ q ∈ eqVisits (wNode c.p base w2') c.i cv c.p.fuel rk,
      w2'.taken.contains q.1 = false := by
    rw [hr0.1, hr0.2.2.1]
    exact fun q hq => ht q (fromVisits_append _ _ _ pre cv _ rk hrk q hq)
  refine writerWP_mono (writerWP_descendLte_reads cv c base hvc c.p.fuel rk w2' ht2) ?_
  intro L w3 ⟨hr23, n, hn, hnl, hlk3, hvisL, _⟩
  rw [hr0.1] at hn hvisL
  have hr03 := ReadsAs.trans _ _ _ _ _ hr0 hr23
  have hnoop := hleaf L n hvisL hn hnl
  unfold pathSize deleteUpward
  wpSimplify
  rw [writerWP_getNode_known L n c _ hlk3]
  have hnoopb : (bitsUnion n.lastBitmap (n.bitsOf cv) == n.lastBitmap) = true := by
    rw [hnoop]; simp
  simp only [hnoopb, ↓reduceIte, writerWP_pure, Bool.not_true, Bool.false_eq_true]
  rw [hr03.1, hr03.2.1]; exact hR

end SIS.Tree
