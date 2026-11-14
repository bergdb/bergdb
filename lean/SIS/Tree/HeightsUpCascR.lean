/-
The fuel after the stop node's cascade from the heights (bergdb 024-22;
putinv's `UpCascFitsOK`, DelStepsCascRoot.lean): the reached form
`UpCascFitsOKR`, proved (`upCascFitsOKR_of`) from a named premise of the upward
loop's end, `UpHolderOK`, to be checked on runs.

`UpHolderOK` at the loop's end w2: every node not taken back holds, by a live
klong now or before the transaction, only nodes not taken back; its time
klongs are at most the transaction's time; the chain's nodes taken back are
the transaction's. With it, the heights' walk at the descent's end (`HtJ` at
w3) gives the walk at the loop's end: the nodes the loop did not change keep
their cached heights; the stop node and the chain's nodes are segment leaves
(the fill at the delete's start, `stopLeaf_of_liveCounts`), of height 0, so
they ask only that what they hold is not taken back. The path's nodes are
distinct (`ht_path_ne`, the kinds' books at w3), so the stop node and the
nodes above it are not the chain's. Then the cascade at the stop node, the
delete's first write that adds heights, adds at most one to the heights of
the nodes not taken back, as in `delFullFitsOKR_of`.
-/
import SIS.Tree.HeightsFitsR
import SIS.Tree.StopLeafLive
import SIS.Tree.HeightsPathNodup

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- The upward loop's end w2 (named premise): every node not taken back holds,
by a live klong now or before the transaction, only nodes not taken back, and
has its time klongs at most the transaction's time; the chain's nodes taken
back are the transaction's. -/
def UpHolderOK (c : Ctx) (B : NodeId) (X : Nat → NodeId) (depth stop : Nat) (w2 : W) : Prop :=
  (∀ y n, w2.nodes.lookup y = some n → w2.taken.contains y = false →
    ∀ cv z, ((cv, z) ∈ n.live ∨ (cv, z) ∈ (n.toPrev (c.i - 1)).live) →
      w2.taken.contains z = false) ∧
  (∀ y n, w2.nodes.lookup y = some n → w2.taken.contains y = false →
    ∀ s, Klong.time s ∈ n.ks → s ≤ c.i) ∧
  (∀ k, stop < k → k ≤ depth → w2.taken.contains (X k) = true → B ≤ X k)

/-- putinv's `UpCascFitsOK` with the merges on, the fill at the delete's start,
the kinds' books and the heights' state at the descent's end (the path ending
at depth), the cached heights the same at the loop's end, and `UpHolderOK`. -/
def UpCascFitsOKR (c : Ctx) (base : View BVal) (KO : KindOracle) (BK : NodeId)
    (H : NodeId → Nat → Prop) : Prop :=
  ∀ (w w3 : W) (B MB : NodeId) (top0 : Top) (pre : List Nat) (cv : Nat) (rk : NodeId)
    (X : Nat → NodeId) (Nn : Nat → KNode) (K : Nat → Nat) (depth stop : Nat) (w2 v : W) (S : KNode),
    c.p.merges = true → LiveCounts c.p (wNode c.p base w) c.i w.top.rootKey →
    KdHtJ c B top0 KO BK H w3 → w3.path.length = depth + 1 → w2.gh = w3.gh →
    UpHolderOK c BK X depth stop w2 →
    2 ≤ c.p.splitAbove → ViewIdsBelow BK c.view → ViewKinds KO BK c → ICEFromKinds c base KO BK →
    X 0 = w.top.rootKey → PutBase c base B → PutInv c base w → RangeOrder (wNode c.p base w) c.i w.top.rootKey →
    SegFits (wNode c.p base w) c.i (c.p.fuel - 1) w.top.rootKey →
    InnerChildrenExist (wNode c.p base w) c.i w.top.rootKey → ReadsAs c.p base w w3 →
    keyWf (pre ++ [cv]) = true →
    segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk →
    (X depth, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
    (∀ i, i ≤ depth → (w3.path[i]?).map (·.2) = some (X i)) →
    (∀ i, 0 < i → i ≤ depth → w3.path[i]? = some (some (K i), X i)) →
    (∀ i, i ≤ depth → w3.nodes.lookup (X i) = some (Nn i)) →
    (∀ i, i ≤ depth → wNode c.p base w (X i) = some (Nn i)) →
    (∀ i, 0 < i → i ≤ depth → (K i, X i) ∈ (Nn (i - 1)).liveAt c.i) →
    bitsUnion (Nn depth).lastBitmap ((Nn depth).bitsOf cv) ≠ (Nn depth).lastBitmap →
    (Nn depth).allKeysIn (bitsUnion (Nn depth).lastBitmap ((Nn depth).bitsOf cv)) = true →
    (Nn depth).leaf = true → 0 < depth → stop < depth →
    (∀ i, stop < i → i < depth →
      (Nn i).allKeysIn (bitsUnion (Nn i).lastBitmap ((Nn i).bitsOf (K (i + 1)))) = true) →
    UpLoopEnd c MB X Nn depth stop w3 w2 S →
    (v = w2 ∨ ∃ s, v = { w2 with trail := s :: w2.trail }) → KdJP c B top0 KO BK w3.path v →
    ((Nn stop).leaf = true ∨ K (stop + 1) ≠ 0) → ¬ DelRoom c (K (stop + 1)) S →
    WriterWP (appendDeleteKlong (X stop) stop (K (stop + 1))) c v
      (fun _ w' => SegFits (wNode c.p base w') c.i c.p.fuel w'.top.rootKey)

set_option maxHeartbeats 3200000 in
/-- `UpCascFitsOKR` from the heights. -/
theorem upCascFitsOKR_of (c : Ctx) (base : View BVal) (KO : KindOracle) (BK : NodeId)
    (H : NodeId → Nat → Prop) (hvo : ViewHtOK H BK c) (hbase : BaseHeights c H base)
    (hHb : ∀ y h, H y h → h ≤ c.p.H) (hpos : 0 < c.i) : UpCascFitsOKR c base KO BK H := by
  intro w w3 B MB top0 pre cv rk X Nn K depth stop w2 v S hm hL hJ3 hlen hgh hU _ _ hk _ hX0 _ hI
    _ _ _ hr03 _ _ _ hpX _ hlk3 hwN hlink _ hall hleafD _ hsd hbetween hLE hvv hJv _ _
  obtain ⟨hU1, hU2, hU3⟩ := hU
  obtain ⟨hT, hTop, -, hP, -, -, hNf, hS, -⟩ := hLE
  obtain ⟨hKd3, hJ⟩ := hJ3
  have hfuel : c.p.H + 2 < c.p.fuel := fuel_gt_H c.p
  -- the state v is w2 but for the trail
  have hvw : v.nodes = w2.nodes ∧ v.gh = w2.gh ∧ v.taken = w2.taken ∧ v.path = w2.path ∧
      v.top = w2.top := by
    rcases hvv with rfl | ⟨s, rfl⟩ <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨hvN, hvG, hvT, hvP, hvTop⟩ := hvw
  have hbv : Book BK c v := hJv.1.2.1
  have hvG3 : v.gh = w3.gh := hvG.trans hgh
  have hvP3 : v.path = w3.path := hvP.trans hP
  -- the times of the path's nodes
  have ht : ∀ i, i ≤ depth → ∀ s, Klong.time s ∈ (Nn i).ks → s ≤ c.i :=
    fun i hi => hI.times _ _ (hwN i hi)
  -- the stop node and the chain's nodes are segment leaves
  have hleafs : ∀ i, stop ≤ i → i ≤ depth → (Nn i).leaf = true := by
    intro i h1 h2
    by_cases hid : i = depth
    · subst hid; exact hleafD
    · cases hl : (Nn i).leaf with
      | true => rfl
      | false =>
        exfalso
        by_cases hi1 : i + 1 = depth
        · exact stopLeaf_of_liveCounts c.p _ c.i _ hL hm X Nn K depth hX0 hwN hlink i (by omega) hl cv
            (ht _ (by omega)) (by rw [hi1]; exact hall)
        · exact stopLeaf_of_liveCounts c.p _ c.i _ hL hm X Nn K depth hX0 hwN hlink i (by omega) hl
            (K (i + 1 + 1)) (ht _ (by omega)) (hbetween (i + 1) (by omega) (by omega))
  -- so their cached heights are 0
  have hh0 : ∀ i, stop ≤ i → i ≤ depth → ∀ g h, (X i, g, h) ∈ w3.gh → h = 0 := by
    intro i h1 h2 g h hm'
    have := hJ.book.leaf (X i) (Nn i) g h (bk_mem_of_lookup _ _ _ (hlk3 i h2)) hm'
    rw [hleafs i h1 h2] at this
    simpa using this.symm
  -- the path's entries
  have hpe : ∀ i, i ≤ depth → ∃ a, w3.path[i]? = some (a, X i) := by
    intro i hi
    have := hpX i hi
    cases he : w3.path[i]? with
    | none => rw [he] at this; cases this
    | some e =>
      rw [he] at this
      simp only [Option.map_some, Option.some.injEq] at this
      exact ⟨e.1, by rw [← this]⟩
  have hall3 : ∀ (d : Nat) (a : Option Nat) (q : NodeId), w3.path[d]? = some (a, q) →
      q ∈ w3.gh.map (·.1) := by
    obtain ⟨a, ha⟩ := hpe depth (Nat.le_refl _)
    exact ht_pathGh_all hJ.book hJ.inv ⟨a, by rw [hlen]; exact ha⟩ (hlk3 depth (Nat.le_refl _))
  -- the path's nodes are distinct
  have hne : ∀ j k, j ≤ depth → k ≤ depth → j ≠ k → X j ≠ X k := by
    intro j k hj hk' hjk
    obtain ⟨a, ha⟩ := hpe j hj
    obtain ⟨b, hb⟩ := hpe k hk'
    exact ht_path_ne hJ.book hvo hJ.inv hk hKd3.2.2 hJ.free hall3 hjk ha hb
  have hnotChain : ∀ j, j ≤ stop → ∀ k, stop < k → k ≤ depth → X j ≠ X k :=
    fun j hj k h1 h2 => hne j k (by omega) h2 (by omega)
  -- a node not taken back at v is not taken back at w3
  have hun3 : ∀ y, v.taken.contains y = false → w3.taken.contains y = false := by
    intro y hy
    by_cases hc : ∃ k, stop < k ∧ k ≤ depth ∧ y = X k
    · obtain ⟨k, h1, h2, rfl⟩ := hc
      obtain ⟨a, ha⟩ := hpe k h2
      exact hJ.free k a (X k) (by rw [hlen]; omega) ha
    · have hny : ∀ k, stop < k → k ≤ depth → y ≠ X k := fun k h1 h2 he => hc ⟨k, h1, h2, he⟩
      rw [← hT y hny, ← hvT]; exact hy
  -- the walk's state at v
  have hiv : HtInv H BK c v := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro x n g h hmem hgm hxf
      have hlv : v.nodes.lookup x = some n := ht_lookup_of_mem hbv hmem
      have hl2 : w2.nodes.lookup x = some n := by rw [← hvN]; exact hlv
      have hxf2 : w2.taken.contains x = false := by rw [← hvT]; exact hxf
      have hgm3 : (x, g, h) ∈ w3.gh := by rw [← hvG3]; exact hgm
      have hkids : ∀ cv z, ((cv, z) ∈ n.live ∨ (cv, z) ∈ (n.toPrev (c.i - 1)).live) →
          v.taken.contains z = false := fun cv z hz => by rw [hvT]; exact hU1 x n hl2 hxf2 cv z hz
      by_cases hc : ∃ i, stop ≤ i ∧ i ≤ depth ∧ x = X i
      · obtain ⟨i, h1, h2, rfl⟩ := hc
        have h0 := hh0 i h1 h2 g h hgm3
        subst h0
        exact ⟨fun cv z hz => ⟨hkids cv z (Or.inl hz), fun h => absurd rfl h⟩,
          fun cv z hz => ⟨hkids cv z (Or.inr hz), fun h => absurd rfl h⟩, hU2 _ n hl2 hxf2⟩
      · have hns : x ≠ X stop := fun he => hc ⟨stop, Nat.le_refl _, by omega, he⟩
        have hnc : ∀ k, stop < k → k ≤ depth → x ≠ X k :=
          fun k h1 h2 he => hc ⟨k, by omega, h2, he⟩
        have hl3 : w3.nodes.lookup x = some n := by rw [← hNf x hns hnc]; exact hl2
        have hx3 : w3.taken.contains x = false := by rw [← hT x hnc]; exact hxf2
        have hN3 := hJ.inv.cache x n g h (bk_mem_of_lookup _ _ _ hl3) hgm3 hx3
        have hht : ∀ z, h ≠ 0 → HasHt H w3 z (h - 1) → HasHt H v z (h - 1) := by
          intro z _ hz
          rcases hz with ⟨g', hg'⟩ | hz
          · exact Or.inl ⟨g', by rw [hvG3]; exact hg'⟩
          · exact Or.inr hz
        exact ⟨fun cv z hz => ⟨hkids cv z (Or.inl hz), fun h0 => hht z h0 ((hN3.1 cv z hz).2 h0)⟩,
          fun cv z hz => ⟨hkids cv z (Or.inr hz), fun h0 => hht z h0 ((hN3.2 cv z hz).2 h0)⟩, hN3.3⟩
    · intro d a q cv y hq hy g h hgm hqf h0
      rw [hvP3] at hq hy
      have := hJ.inv.path d a q cv y hq hy g h (by rw [← hvG3]; exact hgm) (hun3 q hqf) h0
      rcases this with ⟨g', hg'⟩ | hz
      · exact Or.inl ⟨g', by rw [hvG3]; exact hg'⟩
      · exact Or.inr hz
    · intro d a q hq hd
      rw [hvP3] at hq hd
      rw [hvG3]
      exact hJ.inv.pathGh d a q hq hd
    · have hroot : v.top.rootKey = X 0 := by rw [hvTop, hTop, hr03.2.1, hX0]
      rw [hroot, hvT, hT (X 0) (fun k h1 h2 => hne 0 k (by omega) h2 (by omega))]
      have := hJ.inv.rootFree
      rw [hr03.2.1, ← hX0] at this
      exact this
    · intro x hx
      by_cases hc : ∃ k, stop < k ∧ k ≤ depth ∧ x = X k
      · obtain ⟨k, h1, h2, rfl⟩ := hc
        exact hU3 k h1 h2 (by rw [← hvT]; exact hx)
      · have hny : ∀ k, stop < k → k ≤ depth → x ≠ X k := fun k h1 h2 he => hc ⟨k, h1, h2, he⟩
        apply hJ.inv.takenAbove
        rw [← hT x hny, ← hvT]; exact hx
    · intro d a q hq
      rw [hvP3] at hq
      exact hJ.inv.pathSome d a q hq
  -- the path's nodes at the stop node and above are not taken back
  have hpf : PathFreeTo v (stop + 1) := by
    intro d a q hd hq
    rw [hvP3] at hq
    obtain ⟨a', ha'⟩ := hpe d (by omega)
    have hqX : q = X d := by
      rw [ha'] at hq; simp only [Option.some.injEq, Prod.mk.injEq] at hq; exact hq.2.symm
    subst hqX
    rw [hvT, hT (X d) (hnotChain d (by omega))]
    exact hJ.free d a' (X d) (by rw [hlen]; omega) ha'
  -- the cascade at the stop node
  obtain ⟨as, has⟩ := hpe stop (by omega)
  obtain ⟨gs, hs, hms⟩ := kd_tag_of_lookup hJ.book (hlk3 stop (by omega))
  have hpb : PathBelowSB c.p.fuel v := by
    intro d a q hq
    rw [hvP3] at hq
    obtain ⟨⟨q', g', h'⟩, hm', he⟩ := List.mem_map.mp (hall3 d a q hq)
    simp only at he
    subst he
    refine ⟨hbv.bound _ (by rw [hvG3]; exact hm'), fun g2 h2 hm2 => ?_⟩
    rw [hvG3] at hm2
    have hd : d ≤ depth := by have := (List.getElem?_eq_some_iff.mp hq).1; omega
    by_cases hds : d ≤ stop
    · have hqf := hJ.free d a q' (List.getElem?_eq_some_iff.mp hq).1 hq
      have := hJ.bound q' g2 h2 hm2 hqf
      omega
    · obtain ⟨a', ha'⟩ := hpe d hd
      rw [ha'] at hq
      cases hq
      have := hh0 d (by omega) hd g2 h2 hm2
      omega
  have hS0 : SBInvS c.p c.p.fuel (fun y => v.taken.contains y = false) v v :=
    ⟨fun y g' h' hm' hy => Nat.le_trans (hJ.bound y g' h' (by rw [← hvG3]; exact hm') (hun3 y hy))
      (Nat.sub_le _ _), Nat.le_refl _, rfl, fun _ _ _ hm' _ => Or.inl hm'⟩
  have hpxv : v.path[stop]? = some (as, X stop) := by rw [hvP3]; exact has
  refine writerWP_mono (writerWP_and
    (ht_appendDeleteKlong BK (X stop) stop (K (stop + 1)) c v hvo hpos hbv hiv gs hs
      (by rw [hvG3]; exact hms) as hpxv hpf)
    (sbS_appendDeleteKlong c.p.fuel (X stop) stop (K (stop + 1)) c v v (by omega) hS0 hpb as hpxv)) ?_
  rintro _ u ⟨⟨hbu, hiu, hleu, -⟩, hsu⟩
  refine segFits_of_heightsU hbu hiu.cache hvo.heights base hbase c.p.fuel _ ?_
  intro y n hn k' hk'
  rcases hk' with ⟨g', hm'⟩ | hk'
  · have hyu := (ht_wNode_cases hn).1
    exact hsu.1 y g' k' hm' (by rw [← hleu.2]; exact hyu)
  · have := hHb y k' hk'; omega

end SIS.Tree
