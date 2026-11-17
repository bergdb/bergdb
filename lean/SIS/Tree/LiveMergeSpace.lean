/-
The merge's tail where its parent goes `full` and splits in space (bergdb 030-01,
step 3's rest): the parent, not made by the transaction, below an inner parent q
with room for the halves' klongs. A space split leaves no hole: the parent's
last version has more than `splitAbove` klongs, so it was filled though it lost
one, and its halves are filled (`HalfOK`); so the live counts hold after the
merge and no descent is needed. The rest is `MergeTailFullRest3OK`.
-/
import SIS.Tree.LiveMergeMade
import SIS.Tree.LiveDelSpace

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- The halves of the merge's full parent's last version (sorted pairs, more than
`splitAbove` klongs): their live klongs are the last version's, on either side of
the divider, and both are `HalfOK`. -/
theorem halves_mergeLast (c : Ctx) (hMP : MergeParamsOK c.p) (pn last : KNode)
    (pairs : List (Nat × NodeId)) (hleaf : last.leaf = pn.leaf) (hks : last.ks = newKlongs c.i pairs)
    (hs : CvSorted pairs) (hsp : c.p.splitAbove < last.size) :
    (∀ c' z, (c', z) ∈ (halves pn.leaf c.i last []).1.liveAt c.i →
      c' < (halves pn.leaf c.i last []).2.2 ∧ (c', z) ∈ (⟨pn.leaf, last.ks⟩ : KNode).liveAt c.i) ∧
    (∀ c' z, (c', z) ∈ (halves pn.leaf c.i last []).2.1.liveAt c.i →
      ∃ c0, (halves pn.leaf c.i last []).2.2 ≤ c0 ∧
        c' = splitLocalCv pn.leaf (halves pn.leaf c.i last []).2.2 c0 ∧
        (c0, z) ∈ (⟨pn.leaf, last.ks⟩ : KNode).liveAt c.i) ∧
    HalfOK c.p c.i (halves pn.leaf c.i last []).1 ∧ HalfOK c.p c.i (halves pn.leaf c.i last []).2.1 := by
  have hxe : (⟨pn.leaf, last.ks⟩ : KNode) = ⟨pn.leaf, newKlongs c.i pairs⟩ := by rw [hks]
  have hlasteq : (⟨pn.leaf, newKlongs c.i pairs⟩ : KNode) = last := by
    rw [← hks]
    cases last with
    | mk lf ks => simp only at hleaf; rw [hleaf]
  have hlv : (⟨pn.leaf, last.ks⟩ : KNode).lastVersion c.i = last := by
    rw [hxe, KNode.lastVersion_newKlongs_sorted _ _ _ hs, hlasteq]
  have hsz : last.size = pairs.length + 1 := by simp [KNode.size, hks, newKlongs]
  have h2 : 2 ≤ (⟨pn.leaf, last.ks⟩ : KNode).live.length := by
    rw [hxe, KNode.live_newKlongs_sorted _ _ _ hs]
    have := hMP.2.2.1; have := hMP.1
    omega
  have ht : ∀ s, Klong.time s ∈ (⟨pn.leaf, last.ks⟩ : KNode).ks → s ≤ c.i := by
    show ∀ s, Klong.time s ∈ last.ks → s ≤ c.i
    rw [hks]; exact newKlongs_times c.i pairs
  obtain ⟨r, hdiv, _, _, hfh, hsh⟩ := halves_facts_nil c.i (⟨pn.leaf, last.ks⟩ : KNode) h2 ht
  rw [hlv] at hdiv hfh hsh
  have hfill := halves_live_fill c.p hMP pn.leaf c.i pairs [] hs (by rw [hlasteq]; exact hsp)
  rw [hlasteq] at hfill
  obtain ⟨ht1, ht2⟩ := halves_times pn.leaf (⟨pn.leaf, last.ks⟩ : KNode) c.i []
  rw [hlv] at ht1 ht2
  have hm : 2 ≤ c.p.mergeBelow := hMP.1
  have hc1 : c.p.mergeBelow ≤ ((halves pn.leaf c.i last []).1.liveAt c.i).length := by
    rw [KNode.liveAt_of_times _ c.i ht1]; exact hfill.1
  have hc2 : c.p.mergeBelow ≤ ((halves pn.leaf c.i last []).2.1.liveAt c.i).length := by
    rw [KNode.liveAt_of_times _ c.i ht2]; exact hfill.2
  refine ⟨?_, ?_, ⟨fun hE => ?_, by omega, fun _ => hc1⟩, ⟨fun hE => ?_, by omega, fun _ => hc2⟩⟩
  · rw [hdiv]; exact hfh
  · rw [hdiv]; exact hsh
  · rw [hE] at hc1; simp at hc1; omega
  · rw [hE] at hc2; simp at hc2; omega

set_option maxHeartbeats 4000000 in
/-- `writerWP_handleFull_spaceRoom_live` (LiveDelSpace.lean) on the tree with x's
node replaced by its last version (the merge's parent's), and the nodes reached
after: x's halves or nodes reached before, not x. -/
theorem writerWP_handleFull_spaceRoomV_live (d' : Nat) (x q : NodeId) (n qn : KNode) (k1 : Nat)
    (last : KNode) (c : Ctx) (base : View BVal) (w : W)
    (hlk : w.nodes.lookup x = some n)
    (hlq : w.nodes.lookup q = some qn) (hqt : w.taken.contains q = false) (hqx : q ≠ x)
    (hxn : x < w.next) (hqn : q < w.next)
    (hfirst : n.firstTime ≠ some c.i) (hql : qn.leaf = false)
    (hsplit : c.p.splitAbove < last.size)
    (hpq : (w.path[d']?).map (·.2) = some q) (hpk : w.path[d' + 1]? = some (some k1, x))
    (hqwf : klongsWf qn.ks = true) (hqtm : ∀ s, Klong.time s ∈ qn.ks → s ≤ c.i)
    (hroom : qn.size + 3 ≤ c.p.M)
    (hdead : deadOver c.p ([(k1, w.next), ((halves n.leaf c.i last []).2.2, w.next + 2)].foldl
      (fun n (cv, y) => n.add c.i (.key cv y)) qn) = false)
    (hk : (k1, x) ∈ qn.liveAt c.i)
    (hT : TreeOK (updN (wNode c.p base w) x ⟨n.leaf, last.ks⟩) c.i w.top.rootKey)
    (hqR : TReach (updN (wNode c.p base w) x ⟨n.leaf, last.ks⟩) c.i w.top.rootKey q)
    (hn1 : wNode c.p base w w.next = none) (hn2 : wNode c.p base w (w.next + 2) = none)
    (ht1 : w.taken.contains w.next = false) (ht2 : w.taken.contains (w.next + 2) = false)
    (hlinks : ∀ u c' z, TReach (updN (wNode c.p base w) x ⟨n.leaf, last.ks⟩) c.i w.top.rootKey u →
      TLink (updN (wNode c.p base w) x ⟨n.leaf, last.ks⟩) c.i u c' z → z < w.next)
    (hf : ∀ c' z, (c', z) ∈ (halves n.leaf c.i last []).1.liveAt c.i →
      c' < (halves n.leaf c.i last []).2.2 ∧ (c', z) ∈ (⟨n.leaf, last.ks⟩ : KNode).liveAt c.i)
    (hs : ∀ c' z, (c', z) ∈ (halves n.leaf c.i last []).2.1.liveAt c.i →
      ∃ c0, (halves n.leaf c.i last []).2.2 ≤ c0 ∧
        c' = splitLocalCv n.leaf (halves n.leaf c.i last []).2.2 c0 ∧
        (c0, z) ∈ (⟨n.leaf, last.ks⟩ : KNode).liveAt c.i)
    (hfH : HalfOK c.p c.i (halves n.leaf c.i last []).1)
    (hsH : HalfOK c.p c.i (halves n.leaf c.i last []).2.1)
    (hL : LiveEdges c.p (updN (wNode c.p base w) x ⟨n.leaf, last.ks⟩) c.i w.top.rootKey) :
    WriterWP (handleFullWith (fun q more => appendKlongs d' q more) (d' + 1) x [] last false) c w
      (fun _ w' => LiveEdges c.p (wNode c.p base w') c.i w'.top.rootKey ∧
        (∀ z, TReach (wNode c.p base w') c.i w'.top.rootKey z →
          (TReach (updN (wNode c.p base w) x ⟨n.leaf, last.ks⟩) c.i w.top.rootKey z ∨ z = w.next ∨ z = w.next + 2) ∧ z ≠ x) ∧
        w'.top = w.top ∧ w'.taken = w.taken) := by
  have hqy1 : q ≠ w.next := by omega
  have hqy2 : q ≠ w.next + 2 := by omega
  have hxy1 : x ≠ w.next := by omega
  have hxy2 : x ≠ w.next + 2 := by omega
  have h12 : w.next ≠ w.next + 2 := by omega
  obtain ⟨hfl, hsl⟩ := halves_leaf_eq n.leaf c.i last []
  apply writerWP_handleFullWith_space_up_last d' x q n qn k1 last c w hlk hlq hql hfirst hsplit hpq hpk
  intro w1 h1n h1t h1top h1path h1next h1vals
  generalize hout : halves n.leaf c.i last [] = out at hdead hf hs hfH hsH hfl hsl h1n ⊢
  have hlq1 : w1.nodes.lookup q = some qn := by
    rw [h1n]; simp only [hqy1, hqy2, ↓reduceIte]; exact hlq
  refine writerWP_mono (writerWP_appendKlongs_addKeys d' q qn _ c w1 hlq1 (by simp; omega) hdead) ?_
  intro _ w2 hw2
  have h2n : w2.nodes = upsert w1.nodes q ([(k1, w.next), (out.2.2, w.next + 2)].foldl
      (fun n (cv, y) => n.add c.i (.key cv y)) qn) := by rw [hw2]
  have h2t : w2.taken = w1.taken := by rw [hw2]
  have h2top : w2.top = w1.top := by rw [hw2]
  have hlx2 : w2.nodes.lookup x = some n := by
    rw [h2n, lookup_upsert, if_neg (Ne.symm hqx), h1n]
    simp only [hxy1, hxy2, ↓reduceIte]; exact hlk
  rw [writerWP_bind, writerWP_getNode_known x n c w2 hlx2]
  simp only [putNode, writerWP_modify]
  have key : ∀ w3 : W, w3.nodes = upsert w2.nodes x (n.toPrev (c.i - 1)) → w3.taken = w2.taken →
      w3.top = w2.top → LiveEdges c.p (wNode c.p base w3) c.i w3.top.rootKey ∧
        (∀ z, TReach (wNode c.p base w3) c.i w3.top.rootKey z →
          (TReach (updN (wNode c.p base w) x ⟨n.leaf, last.ks⟩) c.i w.top.rootKey z ∨ z = w.next ∨ z = w.next + 2) ∧ z ≠ x) ∧
        w3.top = w.top ∧ w3.taken = w.taken := by
    intro w3 h3n h3t0 h3top0
    have h3t : w3.taken = w.taken := by rw [h3t0, h2t, h1t]
    have h3top : w3.top = w.top := by rw [h3top0, h2top, h1top]
    have hlook : ∀ z, z ≠ x → z ≠ q → z ≠ w.next → z ≠ w.next + 2 →
        w3.nodes.lookup z = w.nodes.lookup z := by
      intro z hzx hzq hz1 hz2
      rw [h3n, lookup_upsert, if_neg hzx, h2n, lookup_upsert, if_neg hzq, h1n]
      simp only [hz1, hz2, ↓reduceIte]
    have hqn' : (updN (wNode c.p base w) x ⟨n.leaf, last.ks⟩) q = some qn := by
      rw [updN_ne _ _ _ _ hqx]
      simp only [wNode, hqt, Bool.false_eq_true, ↓reduceIte, hlq]
    have hLn : (updN (wNode c.p base w) x ⟨n.leaf, last.ks⟩) x = some ⟨n.leaf, last.ks⟩ := updN_self _ _ _
    have hN'q : wNode c.p base w3 q = some ([(k1, w.next), (out.2.2, w.next + 2)].foldl
        (fun n (cv, y) => n.add c.i (.key cv y)) qn) := by
      have hl : w3.nodes.lookup q = some ([(k1, w.next), (out.2.2, w.next + 2)].foldl
          (fun n (cv, y) => n.add c.i (.key cv y)) qn) := by
        rw [h3n, lookup_upsert, if_neg hqx, h2n, lookup_upsert]; simp
      have ht : w3.taken.contains q = false := by rw [h3t]; exact hqt
      simp only [wNode, ht, Bool.false_eq_true, ↓reduceIte, hl]
    have hN'1 : wNode c.p base w3 w.next = some out.1 := by
      have hl : w3.nodes.lookup w.next = some out.1 := by
        rw [h3n, lookup_upsert, if_neg (Ne.symm hxy1), h2n, lookup_upsert, if_neg (Ne.symm hqy1), h1n]
        simp
      have ht : w3.taken.contains w.next = false := by rw [h3t]; exact ht1
      simp only [wNode, ht, Bool.false_eq_true, ↓reduceIte, hl]
    have hN'2 : wNode c.p base w3 (w.next + 2) = some out.2.1 := by
      have hl : w3.nodes.lookup (w.next + 2) = some out.2.1 := by
        rw [h3n, lookup_upsert, if_neg (Ne.symm hxy2), h2n, lookup_upsert, if_neg (Ne.symm hqy2), h1n]
        simp
      have ht : w3.taken.contains (w.next + 2) = false := by rw [h3t]; exact ht2
      simp only [wNode, ht, Bool.false_eq_true, ↓reduceIte, hl]
    have hother : ∀ z, z ≠ x → z ≠ q → z ≠ w.next → z ≠ w.next + 2 →
        wNode c.p base w3 z = (updN (wNode c.p base w) x ⟨n.leaf, last.ks⟩) z := by
      intro z hzx hzq hz1 hz2
      rw [updN_ne _ _ _ _ hzx]
      simp only [wNode, h3t, hlook z hzx hzq hz1 hz2]
    have hn1V : (updN (wNode c.p base w) x ⟨n.leaf, last.ks⟩) w.next = none := by rw [updN_ne _ _ _ _ (Ne.symm hxy1)]; exact hn1
    have hn2V : (updN (wNode c.p base w) x ⟨n.leaf, last.ks⟩) (w.next + 2) = none := by rw [updN_ne _ _ _ _ (Ne.symm hxy2)]; exact hn2
    have hq1wf := KNode.add_key_wf qn c.i k1 w.next hqwf
    have hq1t := KNode.add_times qn c.i (.key k1 w.next) (fun s h => by cases h) hqtm
    have hq' : ∀ c' z, (c', z) ∈ ([(k1, w.next), (out.2.2, w.next + 2)].foldl
        (fun n (cv, y) => n.add c.i (.key cv y)) qn).liveAt c.i →
        (c' = out.2.2 ∧ z = w.next + 2) ∨ (c' ≠ out.2.2 ∧ c' = k1 ∧ z = w.next) ∨
        (c' ≠ out.2.2 ∧ c' ≠ k1 ∧ (c', z) ∈ qn.liveAt c.i) := by
      intro c' z h
      simp only [List.foldl_cons, List.foldl_nil] at h
      rcases KNode.add_key_liveAt_mem _ c.i _ _ hq1wf hq1t c' z h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨h1, h2⟩
      · rcases KNode.add_key_liveAt_mem _ c.i _ _ hqwf hqtm c' z h2 with ⟨h3, h4⟩ | ⟨h3, h4⟩
        · exact Or.inr (Or.inl ⟨h1, h3, h4⟩)
        · exact Or.inr (Or.inr ⟨h1, h3, h4⟩)
    have hq'l : ([(k1, w.next), (out.2.2, w.next + 2)].foldl
        (fun n (cv, y) => n.add c.i (.key cv y)) qn).leaf = qn.leaf := by
      simp only [List.foldl_cons, List.foldl_nil, KNode.add_leaf]
    have hgen := liveEdgesX_spaceSplit_gen c.p (fun _ => False) _ (wNode c.p base w3)
      c.i w.top.rootKey q x w.next (w.next + 2) qn ⟨n.leaf, last.ks⟩ out.1 out.2.1
      ([(k1, w.next), (out.2.2, w.next + 2)].foldl (fun n (cv, y) => n.add c.i (.key cv y)) qn)
      k1 out.2.2 (splitLocalCv n.leaf out.2.2) hT hqR hqn' hk hLn hN'q hq' hN'1 hN'2 hf hs
      (fun z h1 h2 h3 h4 => hother z h1 h2 h3 h4) hn1V hn2V h12
      (by
        intro z hz u c' hu hl
        have := hlinks u c' z hu hl
        rcases hz with hz | hz <;> omega)
      (fun h => h) (fun h => h) hfl hsl hfH hsH hq'l
      (addKeys_liveAt_length c.i [(k1, w.next), (out.2.2, w.next + 2)] qn hqwf hqtm)
      ((liveEdgesX_false_iff _ _ _ _).mpr hL)
    have hR := (treeOK_spaceSplit_gen _ (wNode c.p base w3)
      c.i w.top.rootKey q x w.next (w.next + 2) qn ⟨n.leaf, last.ks⟩ out.1 out.2.1
      ([(k1, w.next), (out.2.2, w.next + 2)].foldl (fun n (cv, y) => n.add c.i (.key cv y)) qn)
      k1 out.2.2 (splitLocalCv n.leaf out.2.2) hT hqR hqn' hk hLn hN'q hq' hN'1 hN'2 hf hs
      (fun z h1 h2 h3 h4 => hother z h1 h2 h3 h4) hn1V hn2V h12
      (by
        intro z hz u c' hu hl
        have := hlinks u c' z hu hl
        rcases hz with hz | hz <;> omega)).2
    refine ⟨?_, ?_, h3top, h3t⟩
    · rw [h3top]
      exact (liveEdgesX_false_iff _ _ _ _).mp hgen
    · rw [h3top]
      intro z hz
      obtain ⟨h1, h2⟩ := hR z hz
      exact ⟨h1, h2⟩
  exact key _ rfl rfl rfl

set_option maxHeartbeats 16000000 in
/-- A merge whose parent p, not made by the transaction, goes `full` and splits
in space (its last version has more than `splitAbove` klongs), below its inner
parent q with room for the halves' klongs and no compaction: no hole after.
Into one node p's last version is filled though it lost a klong
(`liveEdges_of_oneHole`); into two there is no hole before
(`liveEdges_mergeTwo`); the split keeps the live counts
(`writerWP_handleFull_spaceRoomV_live`); p, l and r are left behind, so the
cleanup changes nothing reached. -/
theorem writerWP_mergeTail_liveSpace (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (x : NodeId) (d' : Nat) (p : NodeId)
    (pn xn : KNode) (leftSome : Bool) (l : NodeId) (ln : KNode) (il : Nat) (r : NodeId)
    (rn : KNode) (ir : Nat) (cL cR : Nat) (N : NodeId → Option KNode) (root : NodeId) (nx : Nat)
    (w3 : W) (Hl : NodeId → Prop) (hm : c.p.merges = true) (hMP : MergeParamsOK c.p)
    (hT : TreeOK N c.i root) (hp : TReach N c.i root p) (hpn : N p = some pn)
    (hL : pn.ks[il]? = some (.key cL l)) (hLL : LastLive pn.ks pn.lastBitmap il cL)
    (hR : pn.ks[ir]? = some (.key cR r)) (hRL : LastLive pn.ks pn.lastBitmap ir cR)
    (hclt : cL < cR) (hadj : ∀ cc z, (cc, z) ∈ pn.liveAt c.i → cc ≤ cL ∨ cR ≤ cc)
    (hxlr : x = l ∨ x = r) (hln : N l = some ln) (hrn : N r = some rn)
    (hpt : ∀ s, Klong.time s ∈ pn.ks → s ≤ c.i)
    (hch : ∀ cc z zn, (cc, z) ∈ pn.liveAt c.i → N z = some zn →
      ∀ s, Klong.time s ∈ zn.ks → s ≤ c.i)
    (hN3 : wNode c.p base w3 = N) (h3top : w3.top.rootKey = root) (h3next : w3.next = nx)
    (h3p : w3.nodes.lookup p = some pn) (h3src : ∀ z, (w3.nodes.lookup z).isSome = true → z < nx)
    (hfree : ∀ z, nx ≤ z → N z = none ∧ w3.taken.contains z = false)
    (hfreshT : ∀ z, nx ≤ z → ∀ u c', TReach N c.i root u → ¬ TLink N c.i u c' z)
    (hpleaf : pn.leaf = false) (hll : ln.leaf = xn.leaf) (hrl : rn.leaf = xn.leaf)
    (hlrange : ∀ cc z, (cc, z) ∈ ln.liveAt c.i → cc < cR)
    (hllow : ∀ cc z, (cc, z) ∈ ln.liveAt c.i →
      ((!xn.leaf) = true → cc = 0 ∨ cL < cc) ∧ ((!xn.leaf) = false → cL ≤ cc))
    (hrrange : ∀ cc z, (cc, z) ∈ rn.liveAt c.i →
      ((!xn.leaf) = true → cc = 0 ∨ cR < cc) ∧ ((!xn.leaf) = false → cR ≤ cc))
    (hrup : ∀ k z, (k, z) ∈ pn.liveAt c.i → cR < k → ∀ cc z', (cc, z') ∈ rn.liveAt c.i → cc < k)
    (q : NodeId) (qn : KNode) (k1 : Nat) (hqP : PathLen N c.i root q d') (hNq : N q = some qn)
    (hk : (k1, p) ∈ qn.liveAt c.i) (hqleaf : qn.leaf = false) (h3q : w3.nodes.lookup q = some qn)
    (h3pq : (w3.path[d']?).map (·.2) = some q) (h3pk : w3.path[d' + 1]? = some (some k1, p))
    (hqwf : klongsWf qn.ks = true) (hqtm : ∀ s, Klong.time s ∈ qn.ks → s ≤ c.i)
    (hqroom3 : qn.size + 3 ≤ c.p.M)
    (hqdead2 : ∀ y1 y2 sc, deadOver c.p ([(k1, y1), (sc, y2)].foldl
      (fun n (cv, y) => n.add c.i (.key cv y)) qn) = false)
    (hpnew : pn.firstTime ≠ some c.i)
    (hnB : ¬ MergeParentRoom c pn il cL nx ir cR (mergeM2 c xn ln rn cR nx))
    (hspace : ∀ last, mergeFullLast pn c.i cL nx cR (mergeM2 c xn ln rn cR nx) = some last →
      ¬ (pn.size + mergeParentNeed c.i pn il ir cR (mergeM2 c xn ln rn cR nx) ≤ c.p.M) ∧
        c.p.splitAbove < last.size)
    (hLive : LiveEdgesH c.p N c.i root Hl) (hHl : ∀ y, Hl y → y = x) :
    WriterWP (mergeTail c x (d' + 2) p pn xn leftSome l ln il r rn ir) c w3
      (fun _ w' => LiveEdges c.p (wNode c.p base w') c.i w'.top.rootKey) := by
  -- the tree's facts
  have hpL : (cL, l) ∈ pn.liveAt c.i := by
    rw [KNode.liveAt_of_times pn c.i hpt]
    apply bk_mem_of_lookup
    rw [KNode.live_lookup]
    exact keyLookup_of_last _ _ _ il l hL hLL
  have hpR : (cR, r) ∈ pn.liveAt c.i := by
    rw [KNode.liveAt_of_times pn c.i hpt]
    apply bk_mem_of_lookup
    rw [KNode.live_lookup]
    exact keyLookup_of_last _ _ _ ir r hR hRL
  have hc : cL ≠ cR := Nat.ne_of_lt hclt
  have hlink_l : TLink N c.i p cL l := ⟨pn, hpn, hpL⟩
  have hlink_r : TLink N c.i p cR r := ⟨pn, hpn, hpR⟩
  have hpl : p ≠ l := fun h => hT.no_self_link p cL hp (by rw [← h] at hlink_l; exact hlink_l)
  have hpr : p ≠ r := fun h => hT.no_self_link p cR hp (by rw [← h] at hlink_r; exact hlink_r)
  have hlr : l ≠ r := fun h => hc (hT.oneLink p cL p cR l hp hp hlink_l (by rw [h]; exact hlink_r)).2
  have hlt := hch cL l ln hpL hln
  have hrt := hch cR r rn hpR hrn
  have hcvL : pn.cv? il = some cL := by simp [KNode.cv?, hL]
  have hcvR : pn.cv? ir = some cR := by simp [KNode.cv?, hR]
  have hlt_nx : ∀ y yn, N y = some yn → y < nx := by
    intro y yn hy
    rcases Nat.lt_or_ge y nx with h | h
    · exact h
    · have := (hfree y h).1; rw [this] at hy; cases hy
  have hlnx := hlt_nx l ln hln
  have hrnx := hlt_nx r rn hrn
  have hpnx := hlt_nx p pn hpn
  -- the sibling of the hole is filled: the two hold m live klongs or more
  have hsib : c.p.mergeBelow ≤ ln.live.length + rn.live.length := by
    have hok : ∀ s sn, N s = some sn → (∃ cs, (cs, s) ∈ pn.liveAt c.i) → s ≠ x →
        c.p.mergeBelow ≤ (sn.liveAt c.i).length := by
      intro s sn hs ⟨cs, hcs⟩ hsx
      exact ((hLive.2 p pn cs s sn hp hpn hcs hs).1 (fun h => hsx (hHl s h))).2.2 hpleaf hm
    rcases hxlr with hx | hx
    · have := hok r rn hrn ⟨cR, hpR⟩ (by rw [hx]; exact hlr.symm)
      rw [KNode.liveAt_of_times rn c.i hrt] at this
      omega
    · have := hok l ln hln ⟨cL, hpL⟩ (by rw [hx]; exact hlr)
      rw [KNode.liveAt_of_times ln c.i hlt] at this
      omega
  have hmb : 2 ≤ c.p.mergeBelow := hMP.1
  -- the grandparent q, one above p
  have hpP : PathLen N c.i root p (d' + 1) := PathLen.link hqP ⟨qn, hNq, hk⟩
  have hqp : q ≠ p := by
    intro he; rw [he] at hqP; have := PathLen.depth_unique hT _ _ _ hqP hpP; omega
  have hlP : PathLen N c.i root l (d' + 2) := PathLen.link hpP hlink_l
  have hrP : PathLen N c.i root r (d' + 2) := PathLen.link hpP hlink_r
  have hql : q ≠ l := by
    intro he; rw [he] at hqP; have := PathLen.depth_unique hT _ _ _ hqP hlP; omega
  have hqr : q ≠ r := by
    intro he; rw [he] at hqP; have := PathLen.depth_unique hT _ _ _ hqP hrP; omega
  have hqnx := hlt_nx q qn hNq
  have hqT : w3.taken.contains q = false := by
    have := hN3 ▸ hNq
    unfold wNode at this
    split at this
    · cases this
    · rename_i h; simpa using h
  unfold mergeTail
  simp only [hcvL, hcvR]
  generalize hLM : (ln.firstTime == some c.i) = lMade
  generalize hRM : (rn.firstTime == some c.i) = rMade
  simp only [note, writerWP_bind, writerWP_modify, writerWP_pure]
  generalize hmk : mergeKlongs (!xn.leaf) c.p.mergeMax cR ln.live rn.live = fs
  obtain ⟨first, second⟩ := fs
  wpSplit
  · simp only [writerWP_bind]; exact writerWP_throw _ _ _ _
  wpSplit
  · simp only [writerWP_bind]; exact writerWP_throw _ _ _ _
  rename_i hne1 hne2
  have hrhead : (!xn.leaf) = true → ∃ y0 tl, rn.live = (0, y0) :: tl := by
    intro hin
    rw [hin] at hne2
    simp only [Bool.true_and, Bool.or_eq_true, bne_iff_ne, ne_eq, not_or, Decidable.not_not]
      at hne2
    cases hr' : rn.live with
    | nil => rw [hr'] at hne2; simp at hne2
    | cons a tl =>
      rw [hr'] at hne2
      simp only [List.head?_cons, Option.map_some, Option.some.injEq] at hne2
      exact ⟨a.2, tl, by rw [← hne2.2]⟩
  have hsortE := mrg_mergeList_sorted ln rn c.i (!xn.leaf) cR hlt hrt hlrange hrrange hrhead
  have hmkd : splitMerged (!xn.leaf) c.p.mergeMax (mergeList (!xn.leaf) cR ln.live rn.live) =
      (first, second) := hmk
  have hElen : (mergeList (!xn.leaf) cR ln.live rn.live).length = ln.live.length + rn.live.length :=
    by simpa using congrArg List.length (mergeList_map_snd (!xn.leaf) cR ln.live rn.live)
  -- the new nodes: their klongs name children of l or r, and they are filled
  have hsrcE : ∀ z, z ∈ (mergeList (!xn.leaf) cR ln.live rn.live).map Prod.snd →
      (∃ c0, (c0, z) ∈ ln.liveAt c.i) ∨ (∃ c0, (c0, z) ∈ rn.liveAt c.i) := by
    intro z hz
    rw [mergeList_map_snd] at hz
    rcases List.mem_append.mp hz with h | h
    · obtain ⟨q', hq', he⟩ := List.mem_map.mp h
      exact Or.inl ⟨q'.1, by rw [KNode.liveAt_of_times ln c.i hlt, ← he]; exact hq'⟩
    · obtain ⟨q', hq', he⟩ := List.mem_map.mp h
      exact Or.inr ⟨q'.1, by rw [KNode.liveAt_of_times rn c.i hrt, ← he]; exact hq'⟩
  have hnewT : ∀ ks : List (Nat × NodeId), ∀ s, Klong.time s ∈
      ({ leaf := !!xn.leaf, ks := newKlongs c.i ks } : KNode).ks → s ≤ c.i := by
    intro ks s hs
    simp only [newKlongs, List.mem_cons, Klong.time.injEq, List.mem_map, reduceCtorEq, and_false,
      exists_false, or_false] at hs
    omega
  have hnewSrc : ∀ ks : List (Nat × NodeId), (∀ z, z ∈ ks.map Prod.snd →
      z ∈ (mergeList (!xn.leaf) cR ln.live rn.live).map Prod.snd) → ∀ cc z,
      (cc, z) ∈ ({ leaf := !!xn.leaf, ks := newKlongs c.i ks } : KNode).liveAt c.i →
      (∃ c0, (c0, z) ∈ ln.liveAt c.i) ∨ (∃ c0, (c0, z) ∈ rn.liveAt c.i) := by
    intro ks hks cc z hmem
    have hm2 := liveAt_newKlongs_mem (!!xn.leaf) c.i c.i ks cc z hmem
    exact hsrcE z (hks z (List.mem_map.mpr ⟨(cc, z), hm2, rfl⟩))
  have hnewFill : ∀ ks : List (Nat × NodeId), CvSorted ks → c.p.mergeBelow ≤ ks.length →
      ({ leaf := !!xn.leaf, ks := newKlongs c.i ks } : KNode).liveAt c.i ≠ [] ∧
      c.p.mergeBelow ≤ (({ leaf := !!xn.leaf, ks := newKlongs c.i ks } : KNode).liveAt c.i).length := by
    intro ks hks hlen
    have hcnt : (({ leaf := !!xn.leaf, ks := newKlongs c.i ks } : KNode).liveAt c.i).length =
        ks.length := by
      rw [KNode.liveAt_of_times _ c.i (hnewT ks)]
      exact newKlongs_cnt_of_sorted _ _ _ hks
    refine ⟨fun h0 => ?_, by rw [hcnt]; exact hlen⟩
    have : (({ leaf := !!xn.leaf, ks := newKlongs c.i ks } : KNode).liveAt c.i).length = 0 := by
      rw [h0]; rfl
    omega
  simp only [writerWP_bind, writerWP_modify]
  refine writerWP_mono (writerWP_and (writerWP_ghOf_frame x c _)
    (writerWP_and (writerWP_ghOf_reads x c _ base hvc) (writerWP_ghOf_ghL x c _))) ?_
  intro gh w4 ⟨⟨h4t, h4top, h4n, h4v, h4p, h4m, h4l⟩, hr4, h4gh⟩
  have hlk4 : ∀ y, y ≠ x → w4.nodes.lookup y = w3.nodes.lookup y := h4l
  have hnone3 : ∀ z, nx ≤ z → w3.nodes.lookup z = none := by
    intro z hz
    cases h' : w3.nodes.lookup z with
    | none => rfl
    | some _ => have := h3src z (by rw [h']; rfl); omega
  have hpx : p ≠ x := by rcases hxlr with h | h <;> rw [h] <;> assumption
  have hxnx : x < nx := by rcases hxlr with h | h <;> rw [h] <;> assumption
  have hpT : w3.taken.contains p = false := by
    have := hN3 ▸ hpn
    unfold wNode at this
    split at this
    · cases this
    · rename_i h; simpa using h
  have hNw3 : ∀ y, wNode c.p base w3 y = N y := fun y => by rw [hN3]
  have hcl' : ∀ y, y ≠ l → y ≠ r → ∀ q ∈ [(l, lMade), (r, rMade)], y ≠ (q : NodeId × Bool).1 := by
    intro y hyl hyr q hq
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hq
    rcases hq with h | h <;> rw [h] <;> assumption
  have hne' : ∀ q ∈ [(l, lMade), (r, rMade)], (q : NodeId × Bool).1 ≠ p := by
    intro q hq
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hq
    rcases hq with h | h <;> rw [h]
    · exact Ne.symm hpl
    · exact Ne.symm hpr
  have hlr' : ∀ (q : NodeId × Bool), q ∈ [(l, lMade), (r, rMade)] → q.1 = l ∨ q.1 = r := by
    intro q hq
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hq
    rcases hq with h | h <;> rw [h]
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hnoOld : ∀ z, (z = l ∨ z = r) → ∀ cc, (cc, z) ∈ pn.liveAt c.i → cc ≠ cL → cc ≠ cR → False := by
    intro z hz cc hmem h1 h2
    rcases hz with hz | hz
    · rw [hz] at hmem
      exact h1 (hT.oneLink p cc p cL l hp hp ⟨pn, hpn, hmem⟩ hlink_l).2
    · rw [hz] at hmem
      exact h2 (hT.oneLink p cc p cR r hp hp ⟨pn, hpn, hmem⟩ hlink_r).2
  have hmpT : ∀ il' cL' m1' ir' cR' m2', ∀ s, Klong.time s ∈
      (mergeParentNode pn c.i il' cL' m1' ir' cR' m2').ks → s ≤ c.i := by
    intro il' cL' m1' ir' cR' m2'
    rw [mergeParentNode_eq]
    exact mpNode_times pn c.i _ _ _ _ _ _ _ _ _ (htd_last pn _) hpt
  try dsimp only
  cases lMade <;> cases rMade <;>
    simp only [Bool.false_eq_true, ↓reduceIte, writerWP_bind, writerWP_modify, writerWP_pure,
      replacedBy, writerWP_get]
  all_goals
    refine writerWP_mono (writerWP_and (writerWP_newKey_frame _ _ _ _ c _)
      (writerWP_newKey_ghL _ _ _ _ c _)) ?_
    intro m1 w5 ⟨⟨hm1, h5n, h5t, h5top, h5next, h5v, h5p, h5m⟩, h5gh⟩
    refine writerWP_mono (writerWP_and (writerWP_setMadeFor_frame _ _ c _)
      (writerWP_setMadeFor_gh _ _ c _)) ?_
    intro _ w6 ⟨⟨h6n, h6t, h6top, h6next, h6v, h6p⟩, h6gh⟩
    try dsimp only at hm1 h5n h5t h5top h5next h5v h5p h5m
    have hm1 : m1 = nx := by rw [hm1, h4n, h3next]
    subst hm1
    have hw6p : w6.nodes.lookup p = some pn := by
      rw [h6n, h5n, lookup_append_single_ne _ _ _ _ (by omega), hlk4 p hpx, h3p]
    have hw6m1 : w6.nodes.lookup m1 = some ⟨!!xn.leaf, newKlongs c.i first⟩ := by
      rw [h6n, h5n, h4n, h3next, lookup_append_single_self]
      rw [hlk4 _ (by omega)]
      exact hnone3 m1 (Nat.le_refl _)
    have h6taken : w6.taken = w3.taken := by rw [h6t, h5t, h4t]
    have h6old : ∀ y, y ≠ x → y ≠ m1 → w6.nodes.lookup y = w3.nodes.lookup y := by
      intro y hyx hym
      rw [h6n, h5n, h4n, h3next, lookup_append_single_ne _ _ _ _ hym, hlk4 y hyx]
    have h6next' : w6.next = m1 + 2 := by rw [h6next, h5next, h4n, h3next]
    have h6top' : w6.top.rootKey = root := by rw [h6top, h5top, h4top, h3top]
    have hm1T : w3.taken.contains m1 = false := (hfree m1 (Nat.le_refl _)).2
    have hm1N : N m1 = none := (hfree m1 (Nat.le_refl _)).1
    have hlm1 : l ≠ m1 := by omega
    have hrm1 : r ≠ m1 := by omega
    have hpm1 : p ≠ m1 := by omega
    have hm1R : ¬ TReach N c.i root m1 :=
      not_reach_fresh N c.i root m1 hT hm1N (hfreshT m1 (Nat.le_refl _))
    have hqx : q ≠ x := by rcases hxlr with h | h <;> rw [h] <;> assumption
    have hqm1 : q ≠ m1 := by omega
    have h6path : w6.path = w3.path := by rw [h6p, h5p, h4p]
    have hw6N : ∀ y, y ≠ m1 → wNode c.p base w6 y = N y := by
      intro y hym
      have : wNode c.p base w6 y = wNode c.p base w4 y := by
        simp only [wNode, h6t, h5t, h6n, h5n, h4n, h3next, lookup_append_single_ne _ _ _ _ hym]
      rw [this, hr4.1]; exact congrFun hN3 y
    have hw6q : w6.nodes.lookup q = some qn := by rw [h6old q hqx hqm1, h3q]
    cases hsec : second with
    | none =>
      rw [hsec] at hmkd
      have hfirst : first = mergeList (!xn.leaf) cR ln.live rn.live := splitMerged_one _ _ _ _ hmkd
      simp only [writerWP_bind, writerWP_pure]
      have hm2n : mergeM2 c xn ln rn cR m1 = none := by simp [mergeM2, hmk, hsec]
      rw [hm2n] at hnB hspace
      refine writerWP_mergeParent_fullB p pn (d' + 1) il cL m1 ir cR none c w6 _ hw6p hnB ?_
      intro last compact s7 hlast hcomp
      obtain ⟨hlastT, hleafl, hnoneL, _⟩ := mergeFullLast_liveAt pn c.i cL m1 cR none last hlast hpt
      have hlasteq : (⟨pn.leaf, last.ks⟩ : KNode) = last := by
        cases last with
        | mk lf ks => simp only at hleafl; rw [hleafl]
      have hcLm1 : (cL, m1) ∈ last.liveAt c.i := by
        rw [KNode.liveAt_of_times last c.i hlastT]
        apply bk_mem_of_lookup
        rw [(mergeFullLast_lookup pn c.i cL m1 cR none last hlast).2.1 rfl cL]
        simp
      -- the tree with p's node replaced by its last version
      have hVp : updN (wNode c.p base w6) p last p = some last := updN_self _ _ _
      have hVm1 : updN (wNode c.p base w6) p last m1 = some ⟨!!xn.leaf, newKlongs c.i first⟩ := by
        rw [updN_ne _ _ _ _ (Ne.symm hpm1)]
        simp only [wNode, h6taken, hm1T, Bool.false_eq_true, ↓reduceIte, hw6m1]
      have hVN : ∀ y, y ≠ p → y ≠ m1 → updN (wNode c.p base w6) p last y = N y := by
        intro y hyp hym
        rw [updN_ne _ _ _ _ hyp, hw6N y hym]
      have hmn : ∀ cc z, (cc, z) ∈ ({ leaf := !!xn.leaf, ks := newKlongs c.i first } : KNode).liveAt c.i →
          (cc, z) ∈ mergeList (!xn.leaf) cR ln.live rn.live := by
        intro cc z hm'
        have := liveAt_newKlongs_mem (!!xn.leaf) c.i c.i first cc z hm'
        rw [hfirst] at this; exact this
      have hsrc1 : ∀ z, z ∈ first.map Prod.snd →
          z ∈ (mergeList (!xn.leaf) cR ln.live rn.live).map Prod.snd := by
        intro z hz; rw [hfirst] at hz; exact hz
      have hTV : TreeOK (updN (wNode c.p base w6) p last) c.i root :=
        treeOK_mergeOneAfter N _ c.i root p l r m1 pn ln rn last ⟨!!xn.leaf, newKlongs c.i first⟩
          (!xn.leaf) cL cR hT hp hpn hpL hpR hc hln hrn hlt hrt hm1N (hfreshT m1 (Nat.le_refl _))
          hVm1 hmn hVp (hnoneL rfl) (fun y hyp _ _ hym => hVN y hyp hym)
      have hVreach := mergeV_reach N (updN (wNode c.p base w6) p last) c.i root p l r m1 none pn ln rn
        last cL cR hT hp hpn hpL hpR hln hrn hVp
        (fun cc z hm' => by
          rcases hnoneL rfl cc z hm' with ⟨_, h⟩ | h
          · exact Or.inl h
          · exact Or.inr (Or.inr h))
        (fun m mn hm' hmn' cc z hz => by
          rcases hm' with hm' | hm'
          · rw [hm', hVm1] at hmn'
            cases hmn'
            exact hnewSrc first hsrc1 cc z hz
          · cases hm')
        (fun y hyp _ _ hym _ => hVN y hyp hym) hm1R (fun m hm' => by cases hm')
      have hqRV : TReach (updN (wNode c.p base w6) p last) c.i root q := by
        refine (tReach_of_pathLen_agree N _ c.i root q d' hqP (fun u j hu hj => ?_)).reach
        have hup : u ≠ p := by
          intro he; rw [he] at hu; have := PathLen.depth_unique hT _ _ _ hu hpP; omega
        have hum : u ≠ m1 := fun he => hm1R (he ▸ hu.reach)
        exact hVN u hup hum
      have hVq : updN (wNode c.p base w6) p last q = some qn := by rw [hVN q hqp hqm1, hNq]
      have hy0 : m1 + 2 ≠ m1 := by omega
      have hfreshV : ∀ u c', TReach (updN (wNode c.p base w6) p last) c.i root u →
          ¬ TLink (updN (wNode c.p base w6) p last) c.i u c' (m1 + 2) := by
        intro u c' hu ⟨un, hun, hc'⟩
        obtain ⟨hu1, _, _⟩ := hVreach u hu
        by_cases hup : u = p
        · rw [hup, hVp] at hun; cases hun
          rcases hnoneL rfl c' (m1 + 2) hc' with ⟨_, h⟩ | ⟨h, _, _⟩
          · exact hy0 h
          · exact hfreshT (m1 + 2) (by omega) p c' hp ⟨pn, hpn, h⟩
        · by_cases hum : u = m1
          · rw [hum, hVm1] at hun; cases hun
            rcases hnewSrc first hsrc1 c' (m1 + 2) hc' with ⟨c0, h⟩ | ⟨c0, h⟩
            · exact hfreshT (m1 + 2) (by omega) l c0 (TReach.link hp hlink_l) ⟨ln, hln, h⟩
            · exact hfreshT (m1 + 2) (by omega) r c0 (TReach.link hp hlink_r) ⟨rn, hrn, h⟩
          · rcases hu1 with hu1 | hu1 | hu1
            · rw [hVN u hup hum] at hun
              exact hfreshT (m1 + 2) (by omega) u c' hu1 ⟨un, hun, hc'⟩
            · exact hum hu1
            · cases hu1
      have hLV : LiveEdgesH c.p (updN (wNode c.p base w6) p last) c.i root (fun z => z = p) := by
        have hfirstS : CvSorted first := by rw [hfirst]; exact hsortE
        have hmlen : first.length = ln.live.length + rn.live.length := by rw [hfirst, hElen]
        obtain ⟨hmne, hmfill⟩ := hnewFill first hfirstS (by rw [hmlen]; exact hsib)
        refine liveEdgesH_mergeOne c.p N _ c.i root p l r m1 pn ln rn last
          ⟨!!xn.leaf, newKlongs c.i first⟩ cL cR Hl hT hp hpn hpleaf hpL hpR hln hrn hm1R hVm1
          (hnewSrc first hsrc1) (by show (!!xn.leaf) = ln.leaf; rw [hll, Bool.not_not])
          (by rw [hrl, hll]) hmne hmfill hVp hleafl (hnoneL rfl) (fun h0 => by rw [h0] at hcLm1; cases hcLm1)
          (fun y hyp hyl hyr hym => hVN y hyp hym)
          (fun y hy => by
            have hyx := hHl y hy
            rcases hxlr with h | h
            · exact Or.inl (hyx.trans h)
            · exact Or.inr (hyx.trans h))
          hLive
      have hNlt : ∀ u0 c0 z0, TReach N c.i root u0 → TLink N c.i u0 c0 z0 → z0 < m1 := by
        intro u0 c0 z0 hu0 hl0
        rcases Nat.lt_or_ge z0 m1 with h | h
        · exact h
        · exact absurd hl0 (hfreshT z0 h u0 c0 hu0)
      have hlinksV : ∀ u c' z, TReach (updN (wNode c.p base w6) p last) c.i root u →
          TLink (updN (wNode c.p base w6) p last) c.i u c' z → z < m1 + 2 := by
        intro u c' z hu ⟨un, hun, hc'⟩
        obtain ⟨hu1, _, _⟩ := hVreach u hu
        by_cases hup : u = p
        · rw [hup, hVp] at hun; cases hun
          rcases hnoneL rfl c' z hc' with ⟨_, h⟩ | ⟨h, _, _⟩
          · omega
          · have := hNlt p c' z hp ⟨pn, hpn, h⟩; omega
        · by_cases hum : u = m1
          · rw [hum, hVm1] at hun; cases hun
            rcases hnewSrc first hsrc1 c' z hc' with ⟨c0, h⟩ | ⟨c0, h⟩
            · have := hNlt l c0 z (TReach.link hp hlink_l) ⟨ln, hln, h⟩; omega
            · have := hNlt r c0 z (TReach.link hp hlink_r) ⟨rn, hrn, h⟩; omega
          · rcases hu1 with hu1 | hu1 | hu1
            · rw [hVN u hup hum] at hun
              have := hNlt u c' z hu1 ⟨un, hun, hc'⟩; omega
            · exact absurd hu1 hum
            · cases hu1
      obtain ⟨pairs, hks, hsrt⟩ := mergeFullLast_sorted pn c.i cL m1 cR none last hlast
        (fun _ _ h => by cases h)
      obtain ⟨hnf, hsp⟩ := hspace last hlast
      have hcomp' : compact = false := by rw [hcomp]; exact decide_eq_false hnf
      subst hcomp'
      obtain ⟨hfH1, hsH1, hfH, hsH⟩ := halves_mergeLast c hMP pn last pairs hleafl hks hsrt hsp
      have hsa := hMP.2.2.1
      have hlenV : c.p.splitAbove ≤ ((⟨pn.leaf, last.ks⟩ : KNode).liveAt c.i).length := by
        have hxe : (⟨pn.leaf, last.ks⟩ : KNode) = ⟨pn.leaf, newKlongs c.i pairs⟩ := by rw [hks]
        rw [KNode.liveAt_of_times _ c.i (by rw [hlasteq]; exact hlastT), hxe,
          KNode.live_newKlongs_sorted _ _ _ hsrt]
        have : last.size = pairs.length + 1 := by simp [KNode.size, hks, newKlongs]
        omega
      rw [← hlasteq] at hTV hqRV hLV hVq hlinksV hVreach
      have hVp' : updN (wNode c.p base w6) p ⟨pn.leaf, last.ks⟩ p = some ⟨pn.leaf, last.ks⟩ :=
        updN_self _ _ _
      have hLE : LiveEdges c.p (updN (wNode c.p base w6) p ⟨pn.leaf, last.ks⟩) c.i root :=
        liveEdges_of_oneHole c.p _ c.i root p _ hLV (fun y hy => hy)
          (fun xn' hxn' _ _ => by rw [hVp'] at hxn'; cases hxn'; omega)
          (fun u un cc xn' _ _ _ hxn' hne => by
            rw [hVp'] at hxn'; cases hxn'
            exact ⟨hne, fun _ _ => by omega, fun _ _ => by omega⟩)
      have hnx6 : w6.next = m1 + 2 := h6next'
      unfold handleFull
      show WriterWP (handleFullWith (fun q more => appendKlongs d' q more) (d' + 1) p [] last false)
        c ({ w6 with trail := s7 :: w6.trail } : W) _
      refine writerWP_mono (writerWP_handleFull_spaceRoomV_live d' p q pn qn k1 last c base
        ({ w6 with trail := s7 :: w6.trail } : W) hw6p
        hw6q (by show w6.taken.contains q = false; rw [h6taken]; exact hqT) hqp
        (by show p < w6.next; omega) (by show q < w6.next; omega) hpnew hqleaf hsp
        (by show (w6.path[d']?).map (·.2) = some q; rw [h6path]; exact h3pq)
        (by show w6.path[d' + 1]? = some (some k1, p); rw [h6path]; exact h3pk)
        hqwf hqtm hqroom3 (hqdead2 _ _ _) hk
        (by show TreeOK _ c.i w6.top.rootKey; rw [h6top']; exact hTV)
        (by show TReach _ c.i w6.top.rootKey q; rw [h6top']; exact hqRV)
        (by show wNode c.p base w6 w6.next = none
            rw [hnx6, hw6N (m1 + 2) (by omega)]; exact (hfree _ (by omega)).1)
        (by show wNode c.p base w6 (w6.next + 2) = none
            rw [hnx6, hw6N (m1 + 2 + 2) (by omega)]; exact (hfree _ (by omega)).1)
        (by show w6.taken.contains w6.next = false; rw [hnx6, h6taken]; exact (hfree _ (by omega)).2)
        (by show w6.taken.contains (w6.next + 2) = false
            rw [hnx6, h6taken]; exact (hfree _ (by omega)).2)
        (by show ∀ u c' z, TReach _ c.i w6.top.rootKey u → TLink _ c.i u c' z → z < w6.next
            rw [h6top', hnx6]; exact hlinksV)
        hfH1 hsH1 hfH hsH (by show LiveEdges c.p _ c.i w6.top.rootKey; rw [h6top']; exact hLE)) ?_
      rintro _ w8 ⟨hL8, hR8, h8top, h8t⟩
      change w8.top = w6.top at h8top
      change w8.taken = w6.taken at h8t
      change ∀ z, TReach (wNode c.p base w8) c.i w8.top.rootKey z →
        (TReach (updN (wNode c.p base w6) p ⟨pn.leaf, last.ks⟩) c.i w6.top.rootKey z ∨
          z = w6.next ∨ z = w6.next + 2) ∧ z ≠ p at hR8
      have h8pT : w8.taken.contains p = false := by rw [h8t, h6taken]; exact hpT
      refine writerWP_mono (writerWP_mergeCleanup_wNode p m1 c base hvc _ w8 hne' h8pT) ?_
      rintro _ w9 ⟨h9top, _, _, _, h9w, _, _⟩
      have h8top' : w8.top.rootKey = root := by rw [h8top, h6top']
      rw [h8top', h6top', hnx6] at hR8
      rw [h8top'] at hL8
      have hnot : ∀ z, TReach (wNode c.p base w8) c.i root z → z ≠ p ∧ z ≠ l ∧ z ≠ r := by
        intro z hz
        obtain ⟨h1, hzp⟩ := hR8 z hz
        rcases h1 with hzV | hzy | hzy
        · obtain ⟨_, hzl, hzr⟩ := hVreach z hzV
          exact ⟨hzp, hzl, hzr⟩
        · rw [hzy]; exact ⟨by omega, by omega, by omega⟩
        · rw [hzy]; exact ⟨by omega, by omega, by omega⟩
      rw [h9top, h8top']
      exact liveEdges_of_liveEdgesH c.p _ c.i root (fun _ => False)
        (liveEdgesH_congr_reach c.p (wNode c.p base w8) _ c.i root _
          (liveEdgesH_of_liveEdges c.p _ c.i root _ hL8)
          (fun z hz => by obtain ⟨hzp, hzl, hzr⟩ := hnot z hz; exact h9w z hzp (hcl' z hzl hzr)))
        (fun _ _ h => h.elim) (fun _ _ _ _ _ _ _ _ _ h => h.elim)
    | some ksg =>
      obtain ⟨ks2, g2⟩ := ksg
      rw [hsec] at hmkd
      have hcap : 1 ≤ c.p.mergeMax := by have := hMP.1; have := hMP.2.1; omega
      obtain ⟨yg, hE1, hgs, hE2⟩ := mrg_splitMerged_two (!xn.leaf) c.p.mergeMax hcap _ first ks2 g2 hmkd
      have hElt : c.p.mergeMax < (mergeList (!xn.leaf) cR ln.live rn.live).length := by
        rcases Nat.lt_or_ge c.p.mergeMax (mergeList (!xn.leaf) cR ln.live rn.live).length with h | h
        · exact h
        · exfalso
          unfold splitMerged at hmkd
          simp only [show (mergeList (!xn.leaf) cR ln.live rn.live).length ≤ c.p.mergeMax from h,
            ↓reduceIte, Prod.mk.injEq, reduceCtorEq, and_false] at hmkd
      have hlnL : ∀ q ∈ ln.live, q.1 < cR ∧ ((!xn.leaf) = true → q.1 = 0 ∨ cL < q.1) ∧
          ((!xn.leaf) = false → cL ≤ q.1) := by
        intro q hq
        have hq' : (q.1, q.2) ∈ ln.liveAt c.i := by rw [KNode.liveAt_of_times ln c.i hlt]; exact hq
        exact ⟨hlrange _ _ hq', hllow _ _ hq'⟩
      have hrnR : ∀ q ∈ rn.live, ((!xn.leaf) = true → q.1 = 0 ∨ cR < q.1) ∧
          ((!xn.leaf) = false → cR ≤ q.1) := by
        intro q hq
        have hq' : (q.1, q.2) ∈ rn.liveAt c.i := by rw [KNode.liveAt_of_times rn c.i hrt]; exact hq
        exact hrrange _ _ hq'
      obtain ⟨hgL, _, hgU0⟩ := mrg_two_g (!xn.leaf) cL cR ln.live rn.live
        (((mergeList (!xn.leaf) cR ln.live rn.live).length + 1) / 2) g2 yg hsortE (by omega) hgs
        hclt hlnL hrnR
      have hg2 : g2 ≠ cR → pn.live.lookup g2 = none := by
        intro hne
        cases hlg : pn.live.lookup g2 with
        | none => rfl
        | some z =>
          exfalso
          have hm : (g2, z) ∈ pn.liveAt c.i := by
            rw [KNode.liveAt_of_times pn c.i hpt]; exact bk_mem_of_lookup _ _ _ hlg
          rcases hadj g2 z hm with h1 | h1
          · omega
          · have hgt : cR < g2 := by omega
            have := hgU0 g2 hgt (fun q hq => hrup g2 z hm hgt q.1 q.2 (by
              rw [KNode.liveAt_of_times rn c.i hrt]; exact hq))
            omega
      -- the halves: sorted, filled, naming children of l or r
      have hsortD : CvSorted ((mergeList (!xn.leaf) cR ln.live rn.live).drop
          (((mergeList (!xn.leaf) cR ln.live rn.live).length + 1) / 2)) :=
        hsortE.sublist (List.drop_sublist _ _)
      have hS1 : CvSorted first := by rw [hE1]; exact hsortE.sublist (List.take_sublist _ _)
      have hS2 : CvSorted ks2 := by
        rw [hE2]
        generalize hb : (!xn.leaf) = b at hsortD hgs ⊢
        cases b with
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          exact hsortD
        | true =>
          simp only [↓reduceIte]
          apply renameHead_sorted 0 _ hsortD
          intro q hq
          cases hd : (mergeList true cR ln.live rn.live).drop
              (((mergeList true cR ln.live rn.live).length + 1) / 2) with
          | nil => rw [hd] at hq; simp at hq
          | cons a tl =>
            rw [hd] at hq hgs hsortD
            simp only [List.head?_cons, Option.some.injEq] at hgs
            subst hgs
            simp only [List.tail_cons] at hq
            have := (List.pairwise_cons.mp hsortD).1 q hq
            simp at this; omega
      have hlen1 : first.length = ((mergeList (!xn.leaf) cR ln.live rn.live).length + 1) / 2 := by
        rw [hE1, List.length_take]; omega
      have hlen2 : ks2.length = (mergeList (!xn.leaf) cR ln.live rn.live).length -
          ((mergeList (!xn.leaf) cR ln.live rn.live).length + 1) / 2 := by
        rw [hE2]
        split <;> simp [renameHead_length, List.length_drop]
      have hmb2 := hMP.2.1
      obtain ⟨hmne1, hmfill1⟩ := hnewFill first hS1 (by omega)
      obtain ⟨hmne2, hmfill2⟩ := hnewFill ks2 hS2 (by omega)
      have hsnd := splitMerged_map_snd (!xn.leaf) c.p.mergeMax _ first ks2 g2 hmkd
      have hsrc1 : ∀ z, z ∈ first.map Prod.snd →
          z ∈ (mergeList (!xn.leaf) cR ln.live rn.live).map Prod.snd := by
        intro z hz; rw [← hsnd, List.map_append]; exact List.mem_append_left _ hz
      have hsrc2 : ∀ z, z ∈ ks2.map Prod.snd →
          z ∈ (mergeList (!xn.leaf) cR ln.live rn.live).map Prod.snd := by
        intro z hz; rw [← hsnd, List.map_append]; exact List.mem_append_right _ hz
      simp only [writerWP_bind, writerWP_pure]
      refine writerWP_mono (writerWP_and (writerWP_newKey_frame _ _ _ _ c _)
        (writerWP_newKey_ghL _ _ _ _ c _)) ?_
      intro m2 w7 ⟨⟨hm2, h7n, h7t, h7top, h7next, h7v, h7p, h7m⟩, h7gh⟩
      try simp only [writerWP_bind, writerWP_pure, writerWP_get]
      refine writerWP_mono (writerWP_and (writerWP_setMadeFor_frame _ _ c _)
        (writerWP_setMadeFor_gh _ _ c _)) ?_
      intro _ w8 ⟨⟨h8n, h8t, h8top, h8next, h8v, h8p⟩, h8gh0⟩
      try simp only [writerWP_pure]
      have hm2' : m2 = m1 + 2 := by rw [hm2, h6next']
      subst hm2'
      have hw8p : w8.nodes.lookup p = some pn := by
        rw [h8n, h7n, lookup_append_single_ne _ _ _ _ (by omega), hw6p]
      have hw8m1 : w8.nodes.lookup m1 = some ⟨!!xn.leaf, newKlongs c.i first⟩ := by
        rw [h8n, h7n, lookup_append_single_ne _ _ _ _ (by omega), hw6m1]
      have hw8m2 : w8.nodes.lookup (m1 + 2) = some ⟨!!xn.leaf, newKlongs c.i ks2⟩ := by
        rw [h8n, h7n, h6next', lookup_append_single_self]
        rw [h6old _ (by omega) (by omega)]
        exact hnone3 _ (by omega)
      have h8old : ∀ y, y ≠ x → y ≠ m1 → y ≠ m1 + 2 → w8.nodes.lookup y = w3.nodes.lookup y := by
        intro y hyx hym hym2
        rw [h8n, h7n, h6next', lookup_append_single_ne _ _ _ _ hym2, h6old y hyx hym]
      have h8taken : w8.taken = w3.taken := by rw [h8t, h7t, h6taken]
      have hm2T : w3.taken.contains (m1 + 2) = false := (hfree (m1 + 2) (by omega)).2
      have hm2N : N (m1 + 2) = none := (hfree (m1 + 2) (by omega)).1
      have hm2R : ¬ TReach N c.i root (m1 + 2) :=
        not_reach_fresh N c.i root (m1 + 2) hT hm2N (hfreshT (m1 + 2) (by omega))
      have hlm2 : l ≠ m1 + 2 := by omega
      have hrm2 : r ≠ m1 + 2 := by omega
      have hpm2 : p ≠ m1 + 2 := by omega
      have hm2eq : mergeM2 c xn ln rn cR m1 = some (m1 + 2, g2) := by
        simp [mergeM2, hmk, hsec]
      rw [hm2eq] at hnB hspace
      have h8path : w8.path = w3.path := by rw [h8p, h7p, h6path]
      have hw8N : ∀ y, y ≠ m1 → y ≠ m1 + 2 → wNode c.p base w8 y = N y := by
        intro y hym hym2
        have : wNode c.p base w8 y = wNode c.p base w6 y := by
          simp only [wNode, h8t, h7t, h8n, h7n, h6next', lookup_append_single_ne _ _ _ _ hym2]
        rw [this, hw6N y hym]
      have hw8q : w8.nodes.lookup q = some qn := by rw [h8old q hqx hqm1 (by omega), h3q]
      have h8next' : w8.next = m1 + 4 := by rw [h8next, h7next, h6next']
      have h8top' : w8.top.rootKey = root := by rw [h8top, h7top, h6top']
      refine writerWP_mergeParent_fullB p pn (d' + 1) il cL m1 ir cR (some (m1 + 2, g2)) c w8 _ hw8p hnB ?_
      intro last compact s9 hlast hcomp
      obtain ⟨hlastT, hleafl, _, hsomeL⟩ := mergeFullLast_liveAt pn c.i cL m1 cR _ last hlast hpt
      have hlasteq : (⟨pn.leaf, last.ks⟩ : KNode) = last := by
        cases last with
        | mk lf ks => simp only at hleafl; rw [hleafl]
      have hlk2 := (mergeFullLast_lookup pn c.i cL m1 cR _ last hlast).2.2 (m1 + 2) g2 rfl
      have hlen9 : pn.live.length ≤ last.live.length :=
        live_len_mergeTwo pn last cL cR g2 m1 (m1 + 2) hlk2 (by omega)
          ⟨r, by rw [KNode.live_lookup]; exact keyLookup_of_last _ _ _ ir r hR hRL⟩ hg2
      have hlen10 : (pn.liveAt c.i).length ≤ (last.liveAt c.i).length := by
        rw [KNode.liveAt_of_times pn c.i hpt, KNode.liveAt_of_times last c.i hlastT]; exact hlen9
      have hVp : updN (wNode c.p base w8) p last p = some last := updN_self _ _ _
      have hVm1 : updN (wNode c.p base w8) p last m1 = some ⟨!!xn.leaf, newKlongs c.i first⟩ := by
        rw [updN_ne _ _ _ _ (Ne.symm hpm1)]
        simp only [wNode, h8taken, hm1T, Bool.false_eq_true, ↓reduceIte, hw8m1]
      have hVm2 : updN (wNode c.p base w8) p last (m1 + 2) = some ⟨!!xn.leaf, newKlongs c.i ks2⟩ := by
        rw [updN_ne _ _ _ _ (by omega)]
        simp only [wNode, h8taken, hm2T, Bool.false_eq_true, ↓reduceIte, hw8m2]
      have hVN : ∀ y, y ≠ p → y ≠ m1 → y ≠ m1 + 2 → updN (wNode c.p base w8) p last y = N y := by
        intro y hyp hym hym2
        rw [updN_ne _ _ _ _ hyp, hw8N y hym hym2]
      have hE : (first ++ ks2).map Prod.snd = (ln.live ++ rn.live).map Prod.snd := by
        rw [hsnd, mergeList_map_snd, List.map_append]
      have hTV : TreeOK (updN (wNode c.p base w8) p last) c.i root :=
        treeOK_mergeTwoAfter N _ c.i root p l r m1 (m1 + 2) pn ln rn last
          ⟨!!xn.leaf, newKlongs c.i first⟩ ⟨!!xn.leaf, newKlongs c.i ks2⟩ cL cR g2 first ks2
          hT hp hpn hpL hpR hc hln hrn hlt hrt hm1N (hfreshT m1 (Nat.le_refl _))
          hm2N (hfreshT _ (by omega)) (by omega) hE hVm1
          (fun cc z hm' => liveAt_newKlongs_mem (!!xn.leaf) c.i c.i first cc z hm') hVm2
          (fun cc z hm' => liveAt_newKlongs_mem (!!xn.leaf) c.i c.i ks2 cc z hm') hVp
          (hsomeL (m1 + 2) g2 rfl) (fun y hyp _ _ hym hym2 => hVN y hyp hym hym2)
      have hVreach := mergeV_reach N (updN (wNode c.p base w8) p last) c.i root p l r m1 (some (m1 + 2))
        pn ln rn last cL cR hT hp hpn hpL hpR hln hrn hVp
        (fun cc z hm' => by
          rcases hsomeL (m1 + 2) g2 rfl cc z hm' with ⟨_, h⟩ | ⟨_, h⟩ | h
          · exact Or.inl h
          · exact Or.inr (Or.inl (by rw [h]))
          · exact Or.inr (Or.inr h))
        (fun m mn hm' hmn' cc z hz => by
          rcases hm' with hm' | hm'
          · rw [hm', hVm1] at hmn'
            cases hmn'
            exact hnewSrc first hsrc1 cc z hz
          · simp only [Option.some.injEq] at hm'
            rw [hm', hVm2] at hmn'
            cases hmn'
            exact hnewSrc ks2 hsrc2 cc z hz)
        (fun y hyp _ _ hym hym2 => hVN y hyp hym (fun h => hym2 (by rw [h])))
        hm1R (fun m hm' => by
          simp only [Option.some.injEq] at hm'
          rw [hm']; exact hm2R)
      have hqRV : TReach (updN (wNode c.p base w8) p last) c.i root q := by
        refine (tReach_of_pathLen_agree N _ c.i root q d' hqP (fun u j hu hj => ?_)).reach
        have hup : u ≠ p := by
          intro he; rw [he] at hu; have := PathLen.depth_unique hT _ _ _ hu hpP; omega
        have hum : u ≠ m1 := fun he => hm1R (he ▸ hu.reach)
        have hum2 : u ≠ m1 + 2 := fun he => hm2R (he ▸ hu.reach)
        exact hVN u hup hum hum2
      have hVq : updN (wNode c.p base w8) p last q = some qn := by
        rw [hVN q hqp hqm1 (by omega), hNq]
      have hfreshV : ∀ u c', TReach (updN (wNode c.p base w8) p last) c.i root u →
          ¬ TLink (updN (wNode c.p base w8) p last) c.i u c' (m1 + 4) := by
        intro u c' hu ⟨un, hun, hc'⟩
        obtain ⟨hu1, _, _⟩ := hVreach u hu
        by_cases hup : u = p
        · rw [hup, hVp] at hun; cases hun
          rcases hsomeL (m1 + 2) g2 rfl c' (m1 + 4) hc' with ⟨_, h⟩ | ⟨_, h⟩ | ⟨h, _, _⟩
          · omega
          · omega
          · exact hfreshT (m1 + 4) (by omega) p c' hp ⟨pn, hpn, h⟩
        · by_cases hum : u = m1
          · rw [hum, hVm1] at hun; cases hun
            rcases hnewSrc first hsrc1 c' (m1 + 4) hc' with ⟨c0, h⟩ | ⟨c0, h⟩
            · exact hfreshT (m1 + 4) (by omega) l c0 (TReach.link hp hlink_l) ⟨ln, hln, h⟩
            · exact hfreshT (m1 + 4) (by omega) r c0 (TReach.link hp hlink_r) ⟨rn, hrn, h⟩
          · by_cases hum2 : u = m1 + 2
            · rw [hum2, hVm2] at hun; cases hun
              rcases hnewSrc ks2 hsrc2 c' (m1 + 4) hc' with ⟨c0, h⟩ | ⟨c0, h⟩
              · exact hfreshT (m1 + 4) (by omega) l c0 (TReach.link hp hlink_l) ⟨ln, hln, h⟩
              · exact hfreshT (m1 + 4) (by omega) r c0 (TReach.link hp hlink_r) ⟨rn, hrn, h⟩
            · rcases hu1 with hu1 | hu1 | hu1
              · rw [hVN u hup hum hum2] at hun
                exact hfreshT (m1 + 4) (by omega) u c' hu1 ⟨un, hun, hc'⟩
              · exact hum hu1
              · exact hum2 (Option.some.inj hu1)
      have hLE : LiveEdges c.p (updN (wNode c.p base w8) p last) c.i root :=
        liveEdges_mergeTwo c.p N _ c.i root p l r m1 (m1 + 2) pn ln rn last
          ⟨!!xn.leaf, newKlongs c.i first⟩ ⟨!!xn.leaf, newKlongs c.i ks2⟩ cL cR Hl hT hp hpn hpleaf
          hpL hpR hln hrn hm1R hm2R hVm1 hVm2
          (fun mn hmn cc z hmem => by
            rcases hmn with h | h <;> subst h
            · exact hnewSrc first hsrc1 cc z hmem
            · exact hnewSrc ks2 hsrc2 cc z hmem)
          (by show (!!xn.leaf) = ln.leaf; rw [hll, Bool.not_not])
          (by show (!!xn.leaf) = ln.leaf; rw [hll, Bool.not_not]) (by rw [hrl, hll])
          ⟨hmne1, hmne2⟩ ⟨hmfill1, hmfill2⟩ hVp hleafl
          (fun cc z hm' => by
            rcases hsomeL (m1 + 2) g2 rfl cc z hm' with ⟨_, h⟩ | ⟨_, h⟩ | h
            · exact Or.inl h
            · exact Or.inr (Or.inl h)
            · exact Or.inr (Or.inr h))
          hlen10 (fun y hyp _ _ hym hym2 => hVN y hyp hym hym2)
          (fun y hy => by
            have hyx := hHl y hy
            rcases hxlr with h | h
            · exact Or.inl (hyx.trans h)
            · exact Or.inr (hyx.trans h))
          hLive
      have hLV := liveEdgesH_of_liveEdges c.p _ c.i root (fun z => z = p) hLE
      have hNlt : ∀ u0 c0 z0, TReach N c.i root u0 → TLink N c.i u0 c0 z0 → z0 < m1 := by
        intro u0 c0 z0 hu0 hl0
        rcases Nat.lt_or_ge z0 m1 with h | h
        · exact h
        · exact absurd hl0 (hfreshT z0 h u0 c0 hu0)
      have hlinksV : ∀ u c' z, TReach (updN (wNode c.p base w8) p last) c.i root u →
          TLink (updN (wNode c.p base w8) p last) c.i u c' z → z < m1 + 4 := by
        intro u c' z hu ⟨un, hun, hc'⟩
        obtain ⟨hu1, _, _⟩ := hVreach u hu
        by_cases hup : u = p
        · rw [hup, hVp] at hun; cases hun
          rcases hsomeL (m1 + 2) g2 rfl c' z hc' with ⟨_, h⟩ | ⟨_, h⟩ | ⟨h, _, _⟩
          · omega
          · omega
          · have := hNlt p c' z hp ⟨pn, hpn, h⟩; omega
        · by_cases hum : u = m1
          · rw [hum, hVm1] at hun; cases hun
            rcases hnewSrc first hsrc1 c' z hc' with ⟨c0, h⟩ | ⟨c0, h⟩
            · have := hNlt l c0 z (TReach.link hp hlink_l) ⟨ln, hln, h⟩; omega
            · have := hNlt r c0 z (TReach.link hp hlink_r) ⟨rn, hrn, h⟩; omega
          · by_cases hum2 : u = m1 + 2
            · rw [hum2, hVm2] at hun; cases hun
              rcases hnewSrc ks2 hsrc2 c' z hc' with ⟨c0, h⟩ | ⟨c0, h⟩
              · have := hNlt l c0 z (TReach.link hp hlink_l) ⟨ln, hln, h⟩; omega
              · have := hNlt r c0 z (TReach.link hp hlink_r) ⟨rn, hrn, h⟩; omega
            · rcases hu1 with hu1 | hu1 | hu1
              · rw [hVN u hup hum hum2] at hun
                have := hNlt u c' z hu1 ⟨un, hun, hc'⟩; omega
              · exact absurd hu1 hum
              · exact absurd (Option.some.inj hu1) hum2
      obtain ⟨pairs, hks, hsrt⟩ := mergeFullLast_sorted pn c.i cL m1 cR _ last hlast
        (fun y g hm hgc => by
          simp only [Option.some.injEq, Prod.mk.injEq] at hm
          obtain ⟨_, rfl⟩ := hm
          exact hg2 hgc)
      obtain ⟨hnf, hsp⟩ := hspace last hlast
      have hcomp' : compact = false := by rw [hcomp]; exact decide_eq_false hnf
      subst hcomp'
      obtain ⟨hfH1, hsH1, hfH, hsH⟩ := halves_mergeLast c hMP pn last pairs hleafl hks hsrt hsp
      rw [← hlasteq] at hTV hqRV hLE hVq hlinksV hVreach
      have hnx8 : w8.next = m1 + 4 := h8next'
      unfold handleFull
      show WriterWP (handleFullWith (fun q more => appendKlongs d' q more) (d' + 1) p [] last false)
        c ({ w8 with trail := s9 :: w8.trail } : W) _
      refine writerWP_mono (writerWP_handleFull_spaceRoomV_live d' p q pn qn k1 last c base
        ({ w8 with trail := s9 :: w8.trail } : W) hw8p
        hw8q (by show w8.taken.contains q = false; rw [h8taken]; exact hqT) hqp
        (by show p < w8.next; omega) (by show q < w8.next; omega) hpnew hqleaf hsp
        (by show (w8.path[d']?).map (·.2) = some q; rw [h8path]; exact h3pq)
        (by show w8.path[d' + 1]? = some (some k1, p); rw [h8path]; exact h3pk)
        hqwf hqtm hqroom3 (hqdead2 _ _ _) hk
        (by show TreeOK _ c.i w8.top.rootKey; rw [h8top']; exact hTV)
        (by show TReach _ c.i w8.top.rootKey q; rw [h8top']; exact hqRV)
        (by show wNode c.p base w8 w8.next = none
            rw [hnx8, hw8N (m1 + 4) (by omega) (by omega)]; exact (hfree _ (by omega)).1)
        (by show wNode c.p base w8 (w8.next + 2) = none
            rw [hnx8, hw8N (m1 + 4 + 2) (by omega) (by omega)]; exact (hfree _ (by omega)).1)
        (by show w8.taken.contains w8.next = false; rw [hnx8, h8taken]; exact (hfree _ (by omega)).2)
        (by show w8.taken.contains (w8.next + 2) = false
            rw [hnx8, h8taken]; exact (hfree _ (by omega)).2)
        (by show ∀ u c' z, TReach _ c.i w8.top.rootKey u → TLink _ c.i u c' z → z < w8.next
            rw [h8top', hnx8]; exact hlinksV)
        hfH1 hsH1 hfH hsH (by show LiveEdges c.p _ c.i w8.top.rootKey; rw [h8top']; exact hLE)) ?_
      rintro _ w10 ⟨hL10, hR10, h10top, h10t⟩
      change w10.top = w8.top at h10top
      change w10.taken = w8.taken at h10t
      change ∀ z, TReach (wNode c.p base w10) c.i w10.top.rootKey z →
        (TReach (updN (wNode c.p base w8) p ⟨pn.leaf, last.ks⟩) c.i w8.top.rootKey z ∨
          z = w8.next ∨ z = w8.next + 2) ∧ z ≠ p at hR10
      have h10pT : w10.taken.contains p = false := by rw [h10t, h8taken]; exact hpT
      refine writerWP_mono (writerWP_mergeCleanup_wNode p m1 c base hvc _ w10 hne' h10pT) ?_
      rintro _ w11 ⟨h11top, _, _, _, h11w, _, _⟩
      have h10top' : w10.top.rootKey = root := by rw [h10top, h8top']
      rw [h10top', h8top', hnx8] at hR10
      rw [h10top'] at hL10
      have hnot : ∀ z, TReach (wNode c.p base w10) c.i root z → z ≠ p ∧ z ≠ l ∧ z ≠ r := by
        intro z hz
        obtain ⟨h1, hzp⟩ := hR10 z hz
        rcases h1 with hzV | hzy | hzy
        · obtain ⟨_, hzl, hzr⟩ := hVreach z hzV
          exact ⟨hzp, hzl, hzr⟩
        · rw [hzy]; exact ⟨by omega, by omega, by omega⟩
        · rw [hzy]; exact ⟨by omega, by omega, by omega⟩
      rw [h11top, h10top']
      exact liveEdges_of_liveEdgesH c.p _ c.i root (fun _ => False)
        (liveEdgesH_congr_reach c.p (wNode c.p base w10) _ c.i root _
          (liveEdgesH_of_liveEdges c.p _ c.i root _ hL10)
          (fun z hz => by obtain ⟨hzp, hzl, hzr⟩ := hnot z hz; exact h11w z hzp (hcl' z hzl hzr)))
        (fun _ _ h => h.elim) (fun _ _ _ _ _ _ _ _ _ h => h.elim)

/-! ## At a round: the parent's space split below a parent with room -/

/-- The case of `MergeTailFullRest2OK` that `writerWP_mergeTail_liveSpace`
proves: the merge's parent p, not made by the transaction, goes `full` and
splits in space, below its inner parent q (at depth d - 2) with room for the
halves' klongs and no compaction (whatever the new ids and divider). -/
def MergeFullSpaceRoom (c : Ctx) (v3 : W) (d : Nat) (p : NodeId) (pn xn ln rn : KNode)
    (il cL ir cR : Nat) : Prop :=
  pn.firstTime ≠ some c.i ∧
  (∀ last, mergeFullLast pn c.i cL v3.next cR (mergeM2 c xn ln rn cR v3.next) = some last →
    ¬ (pn.size + mergeParentNeed c.i pn il ir cR (mergeM2 c xn ln rn cR v3.next) ≤ c.p.M) ∧
      c.p.splitAbove < last.size) ∧
  2 ≤ d ∧ ∃ (q : NodeId) (qn : KNode) (k1 : Nat), (v3.path[d - 2]?).map (·.2) = some q ∧
    v3.path[d - 1]? = some (some k1, p) ∧ v3.nodes.lookup q = some qn ∧ qn.leaf = false ∧
    qn.size + 3 ≤ c.p.M ∧ ∀ y1 y2 sc, deadOver c.p ([(k1, y1), (sc, y2)].foldl
      (fun n (cv, y) => n.add c.i (.key cv y)) qn) = false

set_option maxHeartbeats 16000000 in
/-- `MergeTailFullRest2OK`'s case `MergeFullSpaceRoom`: at a round with
`MergeLiveOK`'s facts, the merge's tail ends with the live counts, no hole. -/
theorem writerWP_mergeTail_liveSpaceRound (c : Ctx) (base : View BVal)
    (hvc : ViewCoherent c base) (hm : c.p.merges = true) (hMP : MergeParamsOK c.p)
    {B : NodeId}
    (key : Key) (g h : Nat) (v v1 v3 : W) (d F : Nat) (w0 : W) (k0 : Key) (KO : KindOracle)
    (X : Nat → NodeId) (K : Nat → Nat) (Nn : Nat → KNode) (x p : NodeId)
    (pn xn : KNode)
    (hS : descendToHeight key g h c v = .ok (d, v1)) (hd : 0 < d)
    (hr13 : ReadsAs c.p base v1 v3) (hk13 : ObsKept c v1 v3) (hp13 : v3.path = v1.path)
    (hLH : LiveHoleW key g h c base v)
    (hJ3 : DelInvJ c base w0 k0 F KO B B v3) (hP3 : PathOK c v3 d X K Nn)
    (hx : (v3.path[d]?).map (·.2) = some x) (hpath : (v3.path[d - 1]?).map (·.2) = some p)
    (hplk : v3.nodes.lookup p = some pn) (hpleaf : pn.leaf = false)
    (hxlk : v3.nodes.lookup x = some xn)
    (leftSome : Bool) (l : NodeId) (ln : KNode) (il : Nat) (r : NodeId) (rn : KNode)
    (ir cL cR : Nat) (w3 : W) (hr3 : ReadsAs c.p base v3 w3)
    (h3p : w3.nodes.lookup p = some pn)
    (hsrc3 : ∀ z, (w3.nodes.lookup z).isSome = true → (v3.nodes.lookup z).isSome = true ∨
      (c.view z).isSome = true)
    (hL : pn.ks[il]? = some (.key cL l)) (hLL : LastLive pn.ks pn.lastBitmap il cL)
    (hR : pn.ks[ir]? = some (.key cR r)) (hRL : LastLive pn.ks pn.lastBitmap ir cR) (hclt : cL < cR)
    (hadj : ∀ cc z, (cc, z) ∈ pn.liveAt c.i → cc ≤ cL ∨ cR ≤ cc)
    (hll : ln.leaf = xn.leaf) (hrl : rn.leaf = xn.leaf)
    (hxlr : x = l ∨ x = r) (hln : wNode c.p base v3 l = some ln) (hrn : wNode c.p base v3 r = some rn)
    (hpre3 : v3.nodes <+: w3.nodes) (hpath3 : w3.path = v3.path)
    (hnB : ¬ MergeParentRoom c pn il cL v3.next ir cR (mergeM2 c xn ln rn cR v3.next))
    (hN : MergeFullSpaceRoom c v3 d p pn xn ln rn il cL ir cR) :
    WriterWP (mergeTail c x d p pn xn leftSome l ln il r rn ir) c w3
      (fun res v4 => (res = 1 → LiveHoleW key g (h + 1) c base v4) ∧
        (res ≠ 1 → LiveEdges c.p (wNode c.p base v4) c.i v4.top.rootKey)) := by
  obtain ⟨hpnew, hspace, hd2, q, qn, k1, hq3, hk3', hq3lk, hqleaf, hqroom3, hqdead2⟩ := hN
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 2 := ⟨d - 2, by omega⟩
  have hd2' : d' + 2 - 2 = d' := by omega
  have hd1' : d' + 2 - 1 = d' + 1 := by omega
  rw [hd2'] at hq3
  rw [hd1'] at hk3' hpath
  have hI : PutInv c base v3 := hJ3.1.1.1
  have hRO : RangeOrder (wNode c.p base v3) c.i v3.top.rootKey := hJ3.1.1.2.2.1
  obtain ⟨hX, hK, hS2, hlinkK, _⟩ := id hP3
  have hXi : ∀ i, i ≤ d' + 2 → ∀ z, (v3.path[i]?).map (·.2) = some z → z = X i := by
    intro i hi z hz; have := hX i hi; rw [hz] at this; exact Option.some.inj this
  have hpX := hXi (d' + 1) (by omega) p hpath
  have hqX := hXi d' (by omega) q hq3
  have hxX := hXi (d' + 2) (Nat.le_refl _) x hx
  have hNlk : ∀ i, i ≤ d' + 2 → wNode c.p base v3 (X i) = some (Nn i) := by
    intro i hi
    obtain ⟨a, b⟩ := hS2 i hi
    simp only [wNode, b, Bool.false_eq_true, ↓reduceIte, a]
  have hqn : Nn d' = qn := by
    have := (hS2 d' (by omega)).1; rw [← hqX, hq3lk] at this; exact (Option.some.inj this).symm
  have hpnN : Nn (d' + 1) = pn := by
    have := (hS2 (d' + 1) (by omega)).1; rw [← hpX, hplk] at this; exact (Option.some.inj this).symm
  have hk1 : K (d' + 1) = k1 := by
    have := hK (d' + 1) (by omega) (by omega)
    rw [hk3'] at this
    simp only [Option.some.injEq, Prod.mk.injEq] at this
    exact this.1.symm
  have hkq : (k1, p) ∈ qn.liveAt c.i := by
    have := hlinkK (d' + 1) (by omega) (by omega)
    rw [← hk1, hpX, ← hqn]; exact this
  have hpn : wNode c.p base v3 p = some pn := by rw [hpX, ← hpnN]; exact hNlk _ (by omega)
  have hNq : wNode c.p base v3 q = some qn := by rw [hqX, ← hqn]; exact hNlk _ (by omega)
  have hxn : wNode c.p base v3 x = some xn := by
    obtain ⟨a, b⟩ := hS2 (d' + 2) (Nat.le_refl _)
    rw [← hxX] at a b
    rw [hxlk] at a
    simp only [wNode, b, Bool.false_eq_true, ↓reduceIte, hxlk]
  have hdep : ∀ i, i ≤ d' + 2 → PathLen (wNode c.p base v3) c.i v3.top.rootKey (X i) i :=
    pathOK_depth c base v3 (d' + 2) X K Nn hP3
  have hqP : PathLen (wNode c.p base v3) c.i v3.top.rootKey q d' := by rw [hqX]; exact hdep d' (by omega)
  have hpP : PathLen (wNode c.p base v3) c.i v3.top.rootKey p (d' + 1) := by
    rw [hpX]; exact hdep _ (by omega)
  have hpR := hpP.reach
  have hpRS := tReach_reachS _ c.i _ _ hpR
  have hfree : ∀ z, v3.next ≤ z → wNode c.p base v3 z = none ∧ v3.taken.contains z = false := by
    intro z hz
    have hl : v3.nodes.lookup z = none := by
      cases h' : v3.nodes.lookup z with
      | none => rfl
      | some _ => have := hI.ids.1 z (by rw [h']; rfl); omega
    have ht : v3.taken.contains z = false := by
      cases h' : v3.taken.contains z with
      | false => rfl
      | true => have := hI.ids.2.2.1 z h'; omega
    refine ⟨?_, ht⟩
    simp only [wNode, ht, Bool.false_eq_true, ↓reduceIte, hl, (hI.fresh z hz).1]
  have hfreshT : ∀ z, v3.next ≤ z → ∀ u c', TReach (wNode c.p base v3) c.i v3.top.rootKey u →
      ¬ TLink (wNode c.p base v3) c.i u c' z := by
    intro z hz u c' hu hl
    obtain ⟨un, hun, hc⟩ := hl
    have := hI.links u un c' z (tReach_reachS _ _ _ _ hu) hun hc
    omega
  have hmemL : (cL, l) ∈ pn.liveAt c.i := by
    rw [KNode.liveAt_of_times pn c.i (hI.times p pn hpn)]
    apply bk_mem_of_lookup
    rw [KNode.live_lookup]
    exact keyLookup_of_last _ _ _ il l hL hLL
  have hmemR : (cR, r) ∈ pn.liveAt c.i := by
    rw [KNode.liveAt_of_times pn c.i (hI.times p pn hpn)]
    apply bk_mem_of_lookup
    rw [KNode.live_lookup]
    exact keyLookup_of_last _ _ _ ir r hR hRL
  obtain ⟨hlr1, _⟩ := mrg_child_range (wNode c.p base v3) c.i v3.top.rootKey hRO p pn hpRS hpn
    hpleaf cL l ln hmemL hln
  obtain ⟨hrr1, _⟩ := mrg_child_range (wNode c.p base v3) c.i v3.top.rootKey hRO p pn hpRS hpn
    hpleaf cR r rn hmemR hrn
  have hlr2 := (mrg_child_range (wNode c.p base v3) c.i v3.top.rootKey hRO p pn hpRS hpn
    hpleaf cL l ln hmemL hln).2
  have hrr2 := (mrg_child_range (wNode c.p base v3) c.i v3.top.rootKey hRO p pn hpRS hpn
    hpleaf cR r rn hmemR hrn).2
  -- the round's descent
  obtain ⟨_, _, _, _, _, _, _, _, _, hk01⟩ := writerWP_descendToHeight_rd key g h c v (d' + 2) v1 hS
  have hr01 : ReadsAs c.p base v v1 := writerWP_descendToHeight_readsU key g h c base hvc v _ v1 hS
  have hk03 := hk01.trans hk13
  have hHl : ∀ y, HoleAtW key g h c v y → y = x := by
    intro y hy
    have h1 := hy (d' + 2) v1 hS
    rw [← hp13, hx] at h1
    exact (Option.some.inj h1).symm
  have hN3 : wNode c.p base v3 = wNode c.p base v := by rw [hr13.1, hr01.1]
  have htop3 : v3.top = v.top := hk03.2.2
  have hLive : LiveEdgesH c.p (wNode c.p base v3) c.i v3.top.rootKey (HoleAtW key g h c v) := by
    rw [hN3, htop3]; exact hLH
  have hql : q ≠ l := by
    intro he
    have h2 : PathLen (wNode c.p base v3) c.i v3.top.rootKey l (d' + 1 + 1) :=
      PathLen.link hpP ⟨pn, hpn, hmemL⟩
    rw [← he] at h2; have := PathLen.depth_unique hI.tree _ _ _ hqP h2; omega
  have hqr : q ≠ r := by
    intro he
    have h2 : PathLen (wNode c.p base v3) c.i v3.top.rootKey r (d' + 1 + 1) :=
      PathLen.link hpP ⟨pn, hpn, hmemR⟩
    rw [← he] at h2; have := PathLen.depth_unique hI.tree _ _ _ hqP h2; omega
  have hqp : q ≠ p := by
    intro he; rw [he] at hqP; have := PathLen.depth_unique hI.tree _ _ _ hqP hpP; omega
  have hlrange : ∀ cc z, (cc, z) ∈ ln.liveAt c.i → cc < cR := fun cc z h' => hlr2 cR r hmemR hclt cc z h'
  have hllow : ∀ cc z, (cc, z) ∈ ln.liveAt c.i →
      ((!xn.leaf) = true → cc = 0 ∨ cL < cc) ∧ ((!xn.leaf) = false → cL ≤ cc) := by
    intro cc z h'
    have h1 := hlr1 cc z h'
    rw [hll] at h1
    constructor
    · intro hin
      have hxl : xn.leaf = false := by simpa using hin
      rcases (h1.2 hxl) with h0 | h0
      · exact Or.inl h0
      · rcases Nat.eq_zero_or_pos cL with hc0 | hc0
        · rcases Nat.eq_zero_or_pos cc with hcc | hcc
          · exact Or.inl hcc
          · exact Or.inr (by omega)
        · exact Or.inr (h0 hc0)
    · intro hin
      have hxl : xn.leaf = true := by simpa using hin
      rcases Nat.eq_zero_or_pos cL with hc0 | hc0
      · omega
      · exact h1.1 hxl hc0
  have hrrange : ∀ cc z, (cc, z) ∈ rn.liveAt c.i →
      ((!xn.leaf) = true → cc = 0 ∨ cR < cc) ∧ ((!xn.leaf) = false → cR ≤ cc) := by
    intro cc z h'
    have h1 := hrr1 cc z h'
    rw [hrl] at h1
    constructor
    · intro hin
      have hxl : xn.leaf = false := by simpa using hin
      rcases (h1.2 hxl) with h0 | h0
      · exact Or.inl h0
      · exact Or.inr (h0 (by omega))
    · intro hin
      have hxl : xn.leaf = true := by simpa using hin
      exact h1.1 hxl (by omega)
  refine writerWP_mono (writerWP_mergeTail_liveSpace c base hvc x d' p pn xn leftSome l ln il r rn
    ir cL cR (wNode c.p base v3) v3.top.rootKey v3.next w3 (HoleAtW key g h c v) hm hMP hI.tree hpR
    hpn hL hLL hR hRL hclt hadj hxlr hln hrn (hI.times p pn hpn)
    (fun cc z zn _ hzn => hI.times z zn hzn) hr3.1 (by rw [hr3.2.1]) hr3.2.2.2.2 h3p
    (fun z hz => by
      rcases hsrc3 z hz with h' | h'
      · exact hI.ids.1 z h'
      · exact hI.ids.2.1 z h')
    (fun z hz => ⟨(hfree z hz).1, by rw [hr3.2.2.1]; exact (hfree z hz).2⟩) hfreshT hpleaf hll hrl
    hlrange hllow hrrange (fun k z hk hkc cc z' h' => hrr2 k z hk hkc cc z' h')
    q qn k1 hqP hNq hkq hqleaf (lookup_of_prefix _ _ hpre3 _ _ hq3lk) (by rw [hpath3]; exact hq3)
    (by rw [hpath3]; exact hk3') (hI.wf q qn hNq) (hI.times q qn hNq) hqroom3 hqdead2 hpnew
    hnB hspace hLive hHl) ?_
  intro _ v4 hLE
  exact ⟨fun _ => liveEdgesH_of_liveEdges c.p _ c.i _ _ hLE, fun _ => hLE⟩

/-! ## What is left of `MergeTailFullRest2OK` -/

/-- `MergeTailFullRest2OK` but in its case `MergeFullSpaceRoom` (bergdb 030-01,
step 3's rest): the merge's tail where its parent p goes `full`, and p, not made
by the transaction, is the space root (d = 1) or a segment root (its parent q a
segment leaf), or q has no room for p's new klongs or would compact (the
cascade); or p, made by the transaction, splits in space (in place). -/
def MergeTailFullRest3OK (c : Ctx) (base : View BVal) (B : NodeId) (H : NodeId → Nat → Prop) :
    Prop :=
  ∀ (key : Key) (g h : Nat) (v v1 v3 : W) (d F : Nat) (w0 : W) (k0 : Key) (KO : KindOracle)
    (top0 : Top) (X : Nat → NodeId) (K : Nat → Nat) (Nn : Nat → KNode) (x p : NodeId)
    (pn xn : KNode),
    descendToHeight key g h c v = .ok (d, v1) → 0 < d →
    ReadsAs c.p base v1 v3 → ObsKept c v1 v3 → v3.path = v1.path →
    LiveHoleW key g h c base v →
    DelInvJ c base w0 k0 F KO B B v3 → PutBook c B top0 v3 → PathOK c v3 d X K Nn →
    Book B c v1 → HtInv H B c v1 → PathFreeTo v1 v1.path.length → HtInv H B c v3 →
    (v3.path[d]?).map (·.2) = some x → (v3.path[d - 1]?).map (·.2) = some p →
    v3.nodes.lookup p = some pn → pn.leaf = false → v3.nodes.lookup x = some xn →
    xn.cnt < c.p.mergeBelow →
    ∀ (leftSome : Bool) (l : NodeId) (ln : KNode) (il : Nat) (r : NodeId) (rn : KNode)
      (ir cL cR : Nat) (w3 : W), ReadsAs c.p base v3 w3 →
    w3.nodes.lookup p = some pn → ObsKept c v3 w3 →
    (∀ z, (w3.nodes.lookup z).isSome = true → (v3.nodes.lookup z).isSome = true ∨
      (c.view z).isSome = true) →
    pn.ks[il]? = some (.key cL l) → LastLive pn.ks pn.lastBitmap il cL →
    pn.ks[ir]? = some (.key cR r) → LastLive pn.ks pn.lastBitmap ir cR → cL < cR →
    (∀ cc z, (cc, z) ∈ pn.liveAt c.i → cc ≤ cL ∨ cR ≤ cc) →
    ln.leaf = xn.leaf → rn.leaf = xn.leaf →
    (x = l ∨ x = r) → wNode c.p base v3 l = some ln → wNode c.p base v3 r = some rn →
    v3.nodes <+: w3.nodes → w3.path = v3.path →
    ¬ MergeParentRoom c pn il cL v3.next ir cR (mergeM2 c xn ln rn cR v3.next) →
    ¬ MergeFullTimeRoom c v3 d p pn xn ln rn il cL ir cR →
    ¬ MergeFullMadeTime c v3 pn xn ln rn il cL ir cR →
    ¬ MergeFullSpaceRoom c v3 d p pn xn ln rn il cL ir cR →
    WriterWP (mergeTail c x d p pn xn leftSome l ln il r rn ir) c w3
      (fun res v4 => (res = 1 → LiveHoleW key g (h + 1) c base v4) ∧
        (res ≠ 1 → LiveEdges c.p (wNode c.p base v4) c.i v4.top.rootKey))

/-- `MergeTailFullRest2OK` from its rest: its case `MergeFullSpaceRoom` is proved
(`writerWP_mergeTail_liveSpaceRound`). -/
theorem mergeTailFullRest2OK_of_rest3 (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (hm : c.p.merges = true) (hMP : MergeParamsOK c.p) {B : NodeId} {H : NodeId → Nat → Prop}
    (hF : MergeTailFullRest3OK c base B H) :
    MergeTailFullRest2OK c base B H := by
  intro key g h v v1 v3 d F w0 k0 KO top0 X K Nn x p pn xn hS hd hr13 hk13 hp13 hLH hJ3 hpb3 hP3 hb1
    hi1 hpf1 hi3 hx hpath hplk hpleaf hxlk hcnt leftSome l ln il r rn ir cL cR w3 hr3 h3p hk3 hsrc3
    hL hLL hR hRL hclt hadj hll hrl hxlr hln hrn hpre3 hpath3 hnB hNT hNM
  by_cases hN : MergeFullSpaceRoom c v3 d p pn xn ln rn il cL ir cR
  · exact writerWP_mergeTail_liveSpaceRound c base hvc hm hMP key g h v v1 v3 d F w0 k0 KO
      X K Nn x p pn xn hS hd hr13 hk13 hp13 hLH hJ3 hP3 hx hpath hplk hpleaf hxlk
      leftSome l ln il r rn ir cL cR w3 hr3 h3p hsrc3 hL hLL hR hRL hclt hadj hll hrl hxlr hln hrn
      hpre3 hpath3 hnB hN
  · exact hF key g h v v1 v3 d F w0 k0 KO top0 X K Nn x p pn xn hS hd hr13 hk13 hp13 hLH hJ3 hpb3 hP3
      hb1 hi1 hpf1 hi3 hx hpath hplk hpleaf hxlk hcnt leftSome l ln il r rn ir cL cR w3 hr3 h3p hk3
      hsrc3 hL hLL hR hRL hclt hadj hll hrl hxlr hln hrn hpre3 hpath3 hnB hNT hNM hN

/-- `afterDelete` with the hole (bergdb 030-01, steps 3 and 4): from the call's
facts to `LiveEdges`, premises `MergeTailFullRest3OK`, `MergeParamsOK` and R3
after the merges' loop. -/
theorem writerWP_afterDelete_liveTR3 (key : Key) (g : Nat) (c : Ctx) (base : View BVal)
    (hvc : ViewCoherent c base) (hm : c.p.merges = true) (hMP : MergeParamsOK c.p) (KO : KindOracle)
    (B : NodeId) (hv : ViewIdsBelow B c.view) (hk : ViewKinds KO B c)
    (hICEk : ICEFromKinds c base KO B) (hsa2 : 2 ≤ c.p.splitAbove) (hcap : 1 ≤ c.p.mergeMax)
    (hpos : 0 < c.i) {H : NodeId → Nat → Prop} (hvo : ViewHtOK H B c)
    (hkw : ViewKlongsWf c.p c.view) (top0 : Top) (hB : PutBase c base B)
    (hF : MergeTailFullRest3OK c base B H)
    (v : W) (hJ : DelInvJAE c base KO B B v) (hpb : PutBook c B top0 v) (hhi : HtInv H B c v)
    (hLH : LiveHoleW key g 0 c base v)
    (hR3 : WriterWP (mergeUp key g c.p.fuel 0 false) c v
      (fun merged v' => merged = true → R3At key g c v')) :
    WriterWP (afterDelete key g 0) c v
      (fun _ v' => LiveEdges c.p (wNode c.p base v') c.i v'.top.rootKey) :=
  writerWP_afterDelete_liveTR2 key g c base hvc hm hMP KO B hv hk hICEk hsa2 hcap hpos hvo hkw top0 hB
    (mergeTailFullRest2OK_of_rest3 c base hvc hm hMP hF) v hJ hpb hhi hLH hR3

end SIS.Tree
