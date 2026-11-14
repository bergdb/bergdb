/-
The writer's tree kept by whole operations (bergdb 024-22, `OpTreeOK`), in the
cases that `OpGetOK`'s rules cover (GetFrame.lean, GetSplit.lean,
GetSpaceSplit.lean, GetInPlace.lean): a put into a segment leaf with room
(`writerWP_put_room_seg_tree`), a delete that changes nothing
(`writerWP_del_noop_seg_tree`), a delete's bitmap with the merges off
(`writerWP_del_bitmap_seg_tree`). The descent is the get rules'; the change is
a state rule of the writer's tree (`treeOK_addKey`).
-/
import SIS.Tree.WriterTreeMerge
import SIS.Tree.GetInPlace
import SIS.Tree.WriterTreeMergeTwo

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

theorem tReach_reachS (L : NodeId → Option KNode) (t : Time) (r x : NodeId)
    (h : TReach L t r x) : ReachS L t r x := by
  induction h with
  | root => exact ReachS.root
  | link _ hl ih => obtain ⟨n, hn, hc⟩ := hl; exact ReachS.step _ n _ _ ih hn hc

/-- A key klong naming a fresh node added to a reached node: the tree is kept. -/
theorem treeOK_addKey (N N' : NodeId → Option KNode) (t : Time) (r L y : NodeId) (n : KNode)
    (cv : Nat) (hT : TreeOK N t r) (hLR : TReach N t r L) (hn : N L = some n)
    (hwf : klongsWf n.ks = true) (htimes : ∀ s, Klong.time s ∈ n.ks → s ≤ t)
    (hNL : N' L = some (n.add t (.key cv y))) (hN : ∀ x, x ≠ L → N' x = N x)
    (hy : N y = none) (hfresh : ∀ u c', TReach N t r u → ¬ TLink N t u c' y) : TreeOK N' t r := by
  have hLy : L ≠ y := fun he => by rw [he, hy] at hn; cases hn
  have hyN : N' y = none := by rw [hN _ (Ne.symm hLy)]; exact hy
  have hyR : ¬ TReach N t r y := not_reach_fresh _ _ _ _ hT hy hfresh
  apply treeOK_transfer_gone N N' t r r (fun z => z = y) (fun _ => False) (fun u c' => (u, c')) hT
  · intro z hz; rw [hz]; exact hyR
  · exact Or.inl ⟨rfl, id⟩
  · intro u c' v hu _ hl
    obtain ⟨m, hm, hc⟩ := hl
    by_cases hx : u = L
    · subst hx
      rw [hNL] at hm
      simp only [Option.some.injEq] at hm
      subst hm
      rcases KNode.add_key_liveAt_mem n t cv y hwf htimes c' v hc with ⟨_, hv⟩ | ⟨_, hmem⟩
      · exact Or.inl hv
      · exact Or.inr ⟨id, u, c', hLR, ⟨n, hn, hmem⟩, rfl⟩
    · by_cases huy : u = y
      · rw [huy, hyN] at hm; cases hm
      · rw [hN u hx] at hm
        have huR : TReach N t r u := by
          rcases hu with h | h
          · exact h
          · exact absurd h huy
        exact Or.inr ⟨id, u, c', huR, ⟨m, hm, hc⟩, rfl⟩
  · intro u c' u' c'' z hu _ hu' _ hz hl hl'
    rw [hz] at hl hl'
    have hone : ∀ x d, (TReach N t r x ∨ x = y) → TLink N' t x d y → x = L ∧ d = cv := by
      intro x d hx hl0
      obtain ⟨m, hm, hc⟩ := hl0
      by_cases hxL : x = L
      · subst hxL
        rw [hNL] at hm
        simp only [Option.some.injEq] at hm
        subst hm
        rcases KNode.add_key_liveAt_mem n t cv y hwf htimes d y hc with ⟨hd, _⟩ | ⟨_, hmem⟩
        · exact ⟨rfl, hd⟩
        · exact absurd ⟨n, hn, hmem⟩ (hfresh x d hLR)
      · by_cases hxy : x = y
        · rw [hxy, hyN] at hm; cases hm
        · rw [hN x hxL] at hm
          have hxR : TReach N t r x := by
            rcases hx with h | h
            · exact h
            · exact absurd h hxy
          exact absurd ⟨m, hm, hc⟩ (hfresh x d hxR)
    obtain ⟨h1, h2⟩ := hone u c' hu hl
    obtain ⟨h3, h4⟩ := hone u' c'' hu' hl'
    exact ⟨h1.trans h3.symm, h2.trans h4.symm⟩
  · intro _ _ h; exact h
  · by_cases hr : r = L
    · rw [hr, hNL]; exact ⟨_, rfl⟩
    · rw [hN _ hr]; exact hT.rootKey

/-- The tree is the reads' tree: an operation that only reads keeps it. -/
theorem treeOK_of_readsAs (p : Params) (base : View BVal) (t : Time) (w w' : W)
    (hr : ReadsAs p base w w') (hT : TreeOK (wNode p base w) t w.top.rootKey) :
    TreeOK (wNode p base w') t w'.top.rootKey := by
  rw [hr.1, hr.2.1]; exact hT

/-- `writerWP_put_room_seg` keeps the writer's tree: a put into a segment leaf
with room, below a prefix that is there. -/
theorem writerWP_put_room_seg_tree (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (pre : List Nat) (cv h : Nat) (rk : NodeId) (w : W)
    (hrk : segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk)
    (ht : ∀ q ∈ fromVisits (wNode c.p base w) c.i c.p.fuel (pre ++ [cv]) w.top.rootKey,
      w.taken.contains q.1 = false)
    (hleaf : ∀ L n, (L, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      wNode c.p base w L = some n → n.leaf = true →
      klongsWf n.ks = true ∧ (∀ s, Klong.time s ∈ n.ks → s ≤ c.i) ∧
      n.size + 1 < c.p.M ∧ deadOver c.p (n.add c.i (.key cv w.next)) = false)
    (hwf : ∀ x xn, ReachS (wNode c.p base w) c.i w.top.rootKey x →
      wNode c.p base w x = some xn → klongsWf xn.ks = true)
    (hT : TreeOK (wNode c.p base w) c.i w.top.rootKey)
    (hnext : wNode c.p base w w.next = none)
    (hfresh : ∀ u c', TReach (wNode c.p base w) c.i w.top.rootKey u →
      ¬ TLink (wNode c.p base w) c.i u c' w.next) :
    WriterWP (putKv (.put (pre ++ [cv]) h)) c w (fun _ w' =>
      TreeOK (wNode c.p base w') c.i w'.top.rootKey) := by
  unfold putKv pathClear findRoot pathAdd
  wpSimplify
  generalize hw2 : ({ ({ w with path := [] } : W) with
    path := ([] : List (Option Nat × NodeId)) ++ [(none, w.top.rootKey)] } : W) = w2
  have hr02 : ReadsAs c.p base w w2 := by subst hw2; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  refine writerWP_putSegs_prefix c base hvc (pre ++ [cv]) (some h) cv _ pre w.top.rootKey rk w2
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
  obtain ⟨hwfn, htimes, hroom, hdead⟩ := hleaf L n hvisL hn hnl
  unfold newValue fresh
  wpSimplify
  rw [writerWP_getNode_known L n c _ (by simpa using hlk3)]
  have hnext3 : w3.next = w.next := hr03.2.2.2.2
  have hcond : (decide (n.size + 1 < c.p.M) && !deadOver c.p (n.add c.i (.key cv w3.next))) = true := by
    rw [hnext3, hdead]; simp [hroom]
  simp only [hcond, ↓reduceIte, putNode, writerWP_bind, writerWP_modify, writerWP_pure]
  suffices hfin : ∀ w6 : W, w6.taken = w.taken → w6.top = w.top →
      (∀ x, w6.nodes.lookup x = if x = L then some (n.add c.i (.key cv w.next))
        else w3.nodes.lookup x) →
      TreeOK (wNode c.p base w6) c.i w6.top.rootKey by
    refine hfin _ hr03.2.2.1 hr03.2.1 ?_
    intro x; simp only; rw [lookup_upsert, hnext3]
  intro w6 h6taken h6top h6nodes
  have hLt : w.taken.contains L = false :=
    ht (L, cv) (fromVisits_append _ _ _ pre cv _ rk hrk _ hvisL)
  have hrrk : ReachS (wNode c.p base w) c.i w.top.rootKey rk :=
    segRootR_reach _ _ _ _ hwf pre _ rk ReachS.root hrk
  have hLR : TReach (wNode c.p base w) c.i w.top.rootKey L :=
    reachS_tReach _ _ _ _ (eqVisits_reach _ _ _ cv c.p.fuel rk L cv hrrk hvisL)
  rw [h6top]
  apply treeOK_addKey (wNode c.p base w) (wNode c.p base w6) c.i w.top.rootKey L w.next n cv hT
    hLR hn hwfn htimes
  · simp only [wNode, h6taken, hLt, Bool.false_eq_true, ↓reduceIte, h6nodes]
  · intro x hx
    rw [← hr03.1]
    simp only [wNode, h6taken, h6nodes, hx, ↓reduceIte, hr03.2.2.1]
  · exact hnext
  · exact hfresh

/-- `writerWP_del_noop_seg` keeps the writer's tree: a delete of a key with no
live value only reads. -/
theorem writerWP_del_noop_seg_tree (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (pre : List Nat) (cv : Nat) (rk : NodeId) (w : W)
    (hrk : segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk)
    (ht : ∀ q ∈ fromVisits (wNode c.p base w) c.i c.p.fuel (pre ++ [cv]) w.top.rootKey,
      w.taken.contains q.1 = false)
    (hleaf : ∀ L n, (L, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      wNode c.p base w L = some n → n.leaf = true →
      bitsUnion n.lastBitmap (n.bitsOf cv) = n.lastBitmap)
    (hT : TreeOK (wNode c.p base w) c.i w.top.rootKey) :
    WriterWP (putKv (.del (pre ++ [cv]))) c w (fun _ w' =>
      TreeOK (wNode c.p base w') c.i w'.top.rootKey) := by
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
  exact treeOK_of_readsAs c.p base c.i w w3 hr03 hT

end SIS.Tree
