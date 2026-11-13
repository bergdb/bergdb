/-
The writer's tree kept by whole operations (bergdb 024-22, `OpTreeOK`), in the
cases that `OpGetOK`'s rules cover (GetFrame.lean, GetSplit.lean,
GetSpaceSplit.lean, GetInPlace.lean): a put into a segment leaf with room
(`writerWP_put_room_seg_tree`), a delete that changes nothing
(`writerWP_del_noop_seg_tree`), a delete's bitmap with the merges off
(`writerWP_del_bitmap_seg_tree`). The descent is the get rules'; the change is
a state rule of the writer's tree (`treeOK_addKey`).
-/
import SIS.Tree.WriterTreeInPlace
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

/-- `writerWP_appendDeleteKlong_room_tree` with room needed only where the
bitmap is added (not set in place: the transaction's own bitmap last). -/
theorem writerWP_appendDeleteKlong_room_tree' (base : View BVal) (x : NodeId) (depth cv : Nat)
    (n : KNode) (c : Ctx) (w : W)
    (hT : TreeOK (wNode c.p base w) c.i w.top.rootKey)
    (hlk : w.nodes.lookup x = some n) (hxt : w.taken.contains x = false)
    (hnt : ∀ s, Klong.time s ∈ n.ks → s ≤ c.i)
    (hroom : lastIsDel n.ks = false ∨ n.lastTime ≠ some c.i → n.size + 1 < c.p.M)
    (hdead1 : deadOver c.p (n.setAt (n.size - 1)
      (.del (bitsUnion n.lastBitmap (n.bitsOf cv)))) = false)
    (hdead2 : deadOver c.p (n.add c.i (.del (bitsUnion n.lastBitmap (n.bitsOf cv)))) = false) :
    WriterWP (appendDeleteKlong x depth cv) c w
      (fun _ w' => TreeOK (wNode c.p base w') c.i w'.top.rootKey) := by
  have hwx : wNode c.p base w x = some n := by
    simp only [wNode, hxt, Bool.false_eq_true, ↓reduceIte, hlk]
  have hchange : ∀ n' : KNode, (∀ c' z, (c', z) ∈ n'.liveAt c.i → (c', z) ∈ n.liveAt c.i) →
      TreeOK (wNode c.p base { w with nodes := upsert w.nodes x n' }) c.i w.top.rootKey := by
    intro n' hsub
    apply treeOK_of_node_shrink (wNode c.p base w) _ c.i w.top.rootKey x n n' hT hwx
    · simp only [wNode, hxt, Bool.false_eq_true, ↓reduceIte, lookup_upsert]
    · intro y hy
      simp only [wNode, lookup_upsert, hy, ↓reduceIte]
    · exact hsub
  have hsetAt : ∀ old, n.ks.getLast? = some (.del old) → ∀ c' z,
      (c', z) ∈ (n.setAt (n.size - 1) (.del (bitsUnion n.lastBitmap (n.bitsOf cv)))).liveAt c.i →
      (c', z) ∈ n.liveAt c.i := fun old hold c' z hm =>
    (liveAt_sub_of_lookup n _ c.i cv hnt (KNode.setAt_last_del_times n c.i old _ hold hnt)
      (fun c'' => n.setAt_delete_live_lookup cv c'' old hold) c' z hm).2
  have hadd : ∀ c' z,
      (c', z) ∈ (n.add c.i (.del (bitsUnion n.lastBitmap (n.bitsOf cv)))).liveAt c.i →
      (c', z) ∈ n.liveAt c.i := fun c' z hm =>
    (liveAt_sub_of_lookup n _ c.i cv hnt (KNode.add_times n c.i _ (fun s h => by cases h) hnt)
      (fun c'' => n.add_delete_live_lookup c.i cv c'') c' z hm).2
  unfold appendDeleteKlong
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known x n c w hlk]
  split
  · exact writerWP_throw _ _ _ _
  · generalize hU : bitsUnion n.lastBitmap (n.bitsOf cv) = U at hdead1 hdead2 hsetAt hadd
    cases hno : (U == n.lastBitmap)
    · cases hgl : n.ks.getLast? with
      | none =>
        have hld : lastIsDel n.ks = false := by unfold lastIsDel; rw [hgl]
        have hroom' : n.size + 1 < c.p.M := hroom (Or.inl hld)
        simp only [hroom', hdead2, Bool.not_false, Bool.false_and, Bool.false_eq_true,
          ↓reduceIte, note, putNode, writerWP_bind, writerWP_modify, writerWP_pure]
        exact hchange _ hadd
      | some k =>
        cases k with
        | del old =>
          cases hlt : (n.lastTime == some c.i)
          · have hlt' : n.lastTime ≠ some c.i := by simpa using hlt
            have hroom' : n.size + 1 < c.p.M := hroom (Or.inr hlt')
            simp only [hroom', hdead2, Bool.not_false, Bool.true_and, Bool.false_eq_true,
              ↓reduceIte, note, putNode, writerWP_bind, writerWP_modify, writerWP_pure]
            exact hchange _ hadd
          · simp only [hdead1, Bool.not_false, Bool.true_and, Bool.false_eq_true,
              ↓reduceIte, note, putNode, writerWP_bind, writerWP_modify, writerWP_pure]
            exact hchange _ (hsetAt old hgl)
        | _ =>
          have hld : lastIsDel n.ks = false := by unfold lastIsDel; rw [hgl]
          have hroom' : n.size + 1 < c.p.M := hroom (Or.inl hld)
          simp only [hroom', hdead2, Bool.not_false, Bool.false_and, Bool.false_eq_true,
            ↓reduceIte, note, putNode, writerWP_bind, writerWP_modify, writerWP_pure]
          exact hchange _ hadd
    · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, writerWP_pure]
      exact hT

/-- `writerWP_del_bitmap_seg` keeps the writer's tree: a delete's bitmap in a
segment leaf that keeps a live klong, the merges off. -/
theorem writerWP_del_bitmap_seg_tree (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (pre : List Nat) (cv : Nat) (rk : NodeId) (w : W) (hmerges : c.p.merges = false)
    (hrk : segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk)
    (ht : ∀ q ∈ fromVisits (wNode c.p base w) c.i c.p.fuel (pre ++ [cv]) w.top.rootKey,
      w.taken.contains q.1 = false)
    (hleaf : ∀ L n, (L, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      wNode c.p base w L = some n → n.leaf = true →
      (∀ s, Klong.time s ∈ n.ks → s ≤ c.i) ∧
      bitsUnion n.lastBitmap (n.bitsOf cv) ≠ n.lastBitmap ∧
      n.allKeysIn (bitsUnion n.lastBitmap (n.bitsOf cv)) = false ∧
      deadOver c.p (n.setAt (n.size - 1) (.del (bitsUnion n.lastBitmap (n.bitsOf cv)))) = false ∧
      deadOver c.p (n.add c.i (.del (bitsUnion n.lastBitmap (n.bitsOf cv)))) = false ∧
      (lastIsDel n.ks = false ∨ n.lastTime ≠ some c.i → n.size + 1 < c.p.M))
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
  obtain ⟨htimes, hne, hkeep, hd1, hd2, hroom⟩ := hleaf L n hvisL hn hnl
  have hLt : w.taken.contains L = false :=
    ht (L, cv) (fromVisits_append _ _ _ pre cv _ rk hrk _ hvisL)
  have hT3 : TreeOK (wNode c.p base w3) c.i w3.top.rootKey := treeOK_of_readsAs c.p base c.i w w3 hr03 hT
  unfold pathSize deleteUpward
  wpSimplify
  rw [writerWP_getNode_known L n c _ hlk3]
  have hnb : (bitsUnion n.lastBitmap (n.bitsOf cv) == n.lastBitmap) = false := by
    simpa using hne
  simp only [hnb, Bool.false_eq_true, ↓reduceIte, hkeep, Bool.not_false]
  wpSimplify
  refine writerWP_ghOf_cached L n c _ hlk3 _ (fun gh => ?_)
  refine writerWP_mono (writerWP_appendDeleteKlong_room_tree' base L _ cv n c w3 hT3 hlk3
    (by rw [hr03.2.2.1]; exact hLt) htimes hroom hd1 hd2) ?_
  intro _ w4 hT4
  unfold afterDelete fresh
  wpSimplify
  simp only [hmerges, Bool.false_eq_true, ↓reduceIte, writerWP_pure]
  simp only [Bool.not_false, ↓reduceIte, writerWP_bind, writerWP_get, writerWP_set, writerWP_pure]
  exact hT4

/-- `writerWP_put_spaceSplit_key` keeps the writer's tree: a put into a full
segment leaf that is split in space below an inner parent with room. The ids
from the next one on are in neither the base nor a live klong of the tree. -/
theorem writerWP_put_spaceSplit_seg_tree (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (pre : List Nat) (cv h : Nat) (rk : NodeId) (w : W)
    (hrk : segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk)
    (ht : ∀ q ∈ fromVisits (wNode c.p base w) c.i c.p.fuel (pre ++ [cv]) w.top.rootKey,
      w.taken.contains q.1 = false)
    (hids : (∀ z, (w.nodes.lookup z).isSome = true → z < w.next) ∧
      (∀ z, (c.view z).isSome = true → z < w.next) ∧ (∀ z, w.taken.contains z = true → z < w.next))
    (hbaseF : ∀ z, w.next ≤ z → knodeOf c.p base z = none)
    (hinner : ∀ m, wNode c.p base w rk = some m → m.leaf = false)
    (hleaf : ∀ L n, (L, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      wNode c.p base w L = some n → n.leaf = true →
      (∀ s, Klong.time s ∈ n.ks → s ≤ c.i) ∧ c.p.M ≤ n.size + 1 ∧
      n.firstTime ≠ some c.i ∧ c.p.splitAbove < (n.lastVersion c.i).size ∧ n.live ≠ [])
    (hparent : ∀ q qn, (q, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      wNode c.p base w q = some qn → qn.leaf = false →
      (∀ s, Klong.time s ∈ qn.ks → s ≤ c.i) ∧ qn.size + 2 + 1 ≤ c.p.M ∧
      ∀ a y b z, deadOver c.p ((qn.add c.i (.key a y)).add c.i (.key b z)) = false)
    (hwf : ∀ x xn, ReachS (wNode c.p base w) c.i w.top.rootKey x →
      wNode c.p base w x = some xn → klongsWf xn.ks = true)
    (hT : TreeOK (wNode c.p base w) c.i w.top.rootKey)
    (hfreshT : ∀ z, w.next ≤ z → ∀ u c', TReach (wNode c.p base w) c.i w.top.rootKey u →
      ¬ TLink (wNode c.p base w) c.i u c' z) :
    WriterWP (putKv (.put (pre ++ [cv]) h)) c w (fun _ w' =>
      TreeOK (wNode c.p base w') c.i w'.top.rootKey) := by
  obtain ⟨hidn, hidv, hidt⟩ := hids
  unfold putKv pathClear findRoot pathAdd
  wpSimplify
  generalize hw2 : ({ ({ w with path := [] } : W) with
    path := ([] : List (Option Nat × NodeId)) ++ [(none, w.top.rootKey)] } : W) = w2
  have hr02 : ReadsAs c.p base w w2 := by subst hw2; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  have hw2n : w2.nodes = w.nodes := by subst hw2; rfl
  refine writerWP_putSegs_prefix_src c base hvc (pre ++ [cv]) (some h) cv _ pre w.top.rootKey rk w2
    (by rw [hr02.1, hr02.2.2.1]; exact ht) (by rw [hr02.1]; exact hrk) (by subst hw2; simp) ?_
  intro w2' hr2' hp2' hsrc2'
  have hr0 := ReadsAs.trans _ _ _ _ _ hr02 hr2'
  unfold setValue
  wpSimplify
  have ht2 : ∀ q ∈ eqVisits (wNode c.p base w2') c.i cv c.p.fuel rk,
      w2'.taken.contains q.1 = false := by
    rw [hr0.1, hr0.2.2.1]
    exact fun q hq => ht q (fromVisits_append _ _ _ pre cv _ rk hrk q hq)
  refine writerWP_mono (writerWP_and
    (writerWP_descendLte_path cv c base hvc c.p.fuel rk w2' ht2 hp2')
    (writerWP_descendLte_cache cv c base hvc c.p.fuel rk w2' ht2)) ?_
  intro L w3 ⟨⟨hr23, n, hn, hnl, hlk3, hvisL, _, hdp⟩, ⟨hcache3, hsrc3, _⟩⟩
  rw [hr0.1] at hn hvisL hcache3
  have hr03 := ReadsAs.trans _ _ _ _ _ hr0 hr23
  obtain ⟨htimes, hfull, hfirst, hsplit, hlive⟩ := hleaf L n hvisL hn hnl
  have hnext3 : w3.next = w.next := hr03.2.2.2.2
  rcases hdp with ⟨hLrk, _⟩ | ⟨pre', q, k1, qn, fd, hp3, hlast, hq, hql, hqs, hc, hy, hqv⟩
  · subst hLrk
    rw [hinner n hn] at hnl
    cases hnl
  rw [hr0.1] at hq hqv
  obtain ⟨hqt, hroomq, hdeadq⟩ := hparent q qn hqv hq hql
  unfold newValue fresh
  wpSimplify
  rw [writerWP_getNode_known L n c _ (by simpa using hlk3)]
  have hcond : (decide (n.size + 1 < c.p.M) && !deadOver c.p (n.add c.i (.key cv w3.next))) = false := by
    have : ¬ n.size + 1 < c.p.M := by omega
    simp [this]
  simp only [hcond, Bool.false_eq_true, ↓reduceIte, pathSize, writerWP_bind, writerWP_get,
    writerWP_pure]
  have hsrcw3 : ∀ z, (w3.nodes.lookup z).isSome = true → z < w.next := by
    intro z hz
    rcases hsrc3 z hz with h1 | h1
    · rcases hsrc2' z h1 with h2 | h2
      · rw [hw2n] at h2; exact hidn z h2
      · exact hidv z h2
    · exact hidv z h1
  have hne : w2'.path ++ pre' ≠ [] := by
    intro he
    have : w2'.path = [] := (List.append_eq_nil_iff.mp he).1
    rw [this] at hp2'
    simp at hp2'
  obtain ⟨d', hd'⟩ : ∃ d', (w2'.path ++ pre').length = d' + 1 := by
    cases h' : (w2'.path ++ pre').length with
    | zero => exact absurd (List.eq_nil_of_length_eq_zero h') hne
    | succ k => exact ⟨k, rfl⟩
  have hlen : w3.path.length - 1 = d' + 1 := by
    rw [hp3]; simp only [List.append_assoc, List.length_append, List.length_singleton] at hd' ⊢
    omega
  have hpq : (w3.path[d']?).map (·.2) = some q := by
    rw [hp3, List.append_assoc, ← List.append_assoc w2'.path pre' [(some k1, L)],
      List.getElem?_append_left (by omega)]
    rw [List.getLast?_eq_getElem?] at hlast
    rw [hd'] at hlast
    simpa using hlast
  have hpk : w3.path[d' + 1]? = some (some k1, L) := by
    rw [hp3, List.append_assoc, ← List.append_assoc w2'.path pre' [(some k1, L)],
      List.getElem?_append_right (by omega), hd']
    simp
  have hlq : w3.nodes.lookup q = some qn := hcache3 q qn hqv hq
  have hqL : q ≠ L := by
    intro hqL'
    rw [hqL'] at hq
    rw [hn] at hq
    cases hq
    rw [hnl] at hql
    cases hql
  rw [hlen]
  -- the tree's facts
  have hrrk : ReachS (wNode c.p base w) c.i w.top.rootKey rk :=
    segRootR_reach _ _ _ _ hwf pre _ rk ReachS.root hrk
  have hrq : ReachS (wNode c.p base w) c.i w.top.rootKey q :=
    eqVisits_reach _ _ _ cv c.p.fuel rk q cv hrrk hqv
  have hk1 : (k1, L) ∈ qn.live := by
    have := KNode.searchLte_mem qn c.i cv fd hqs
    rw [KNode.liveAt_of_times qn c.i hqt, hc, hy] at this
    exact this
  have hLt : w.taken.contains L = false :=
    ht (L, cv) (fromVisits_append _ _ _ pre cv _ rk hrk _ hvisL)
  have hqt' : w.taken.contains q = false :=
    ht (q, cv) (fromVisits_append _ _ _ pre cv _ rk hrk _ hqv)
  obtain ⟨r0, hr0'⟩ : ∃ r0, (n.live.drop (n.live.length / 2)).head? = some r0 := by
    cases hd : (n.live.drop (n.live.length / 2)).head? with
    | some r0 => exact ⟨r0, rfl⟩
    | none =>
      exfalso
      rw [List.head?_eq_none_iff, List.drop_eq_nil_iff] at hd
      have : n.live.length ≠ 0 := fun h0 => hlive (List.eq_nil_of_length_eq_zero h0)
      omega
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
  suffices hfin : ∀ w4 : W, w4.taken = w3.taken → w4.nodes = w3.nodes → w4.path = w3.path →
      w4.next = w.next + 2 → w4.top = w3.top →
      WriterWP (appendKlongs (d' + 1) L [(cv, w.next)]) c w4
        (fun _ w' => TreeOK (wNode c.p base w') c.i w'.top.rootKey) by
    rw [hnext3]
    exact hfin _ rfl rfl rfl (by simp) rfl
  intro w4 h4t h4n h4p h4next h4top
  have hW4 : wNode c.p base w4 = wNode c.p base w := by
    rw [← hr03.1]; funext x; simp only [wNode, h4t, h4n]
  have h4tw : w4.taken = w.taken := h4t.trans hr03.2.2.1
  have h4topw : w4.top = w.top := h4top.trans hr03.2.1
  have htn : ∀ z, w.next ≤ z → w4.taken.contains z = false := by
    intro z hz
    rw [h4tw]
    cases h' : w.taken.contains z with
    | false => rfl
    | true => have := hidt z h'; omega
  apply writerWP_appendKlongs_spaceSplit_tree base d' L q n qn k1 cv w.next c w4 r0
  · rw [hW4, h4topw]; exact hT
  · rw [h4n]; exact hlk3
  · rw [h4n]; exact hlq
  · rw [h4tw]; exact hLt
  · rw [h4tw]; exact hqt'
  · exact hqL
  · exact hql
  · exact hfirst
  · omega
  · exact hsplit
  · rw [h4p]; exact hpq
  · rw [h4p]; exact hpk
  · exact hroomq
  · exact fun _ _ _ => hdeadq _ _ _ _
  · rw [KNode.liveAt_of_times qn c.i hqt]; exact hk1
  · rw [hW4, h4topw]; exact reachS_tReach _ _ _ _ hrq
  · exact hnl
  · exact hr0'
  · exact htimes
  · exact hqt
  · exact hwf q qn hrq hq
  · rw [hW4, h4next]; exact hfree _ (by omega)
  · rw [hW4, h4next]; exact hfree _ (by omega)
  · rw [hW4]; exact hfree _ (Nat.le_refl _)
  · rw [h4next]; exact htn _ (by omega)
  · rw [h4next]; exact htn _ (by omega)
  · rw [h4next]; omega
  · rw [h4next]; omega
  · intro z hz u c' hu
    rw [hW4, h4topw] at *
    rw [h4next] at hz
    exact hfreshT z (by omega) u c' hu

end SIS.Tree
