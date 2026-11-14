/-
The upward delete's stop node is a segment leaf when the merges are on
(bergdb 024-22; 024-12's follow-ups, the LE-b probe
12-tree-model/leb-probe.lean.txt): from the fill at the delete's start
(latest's `LiveCounts`, LiveCounts.lean), a node an inner node names has
`mergeBelow` ≥ 2 live klongs, so it is not one that the delete empties
(`stopLeaf_of_liveCounts`). The climb passes only nodes the delete empties,
so the stop node, the parent of one, is no inner node: neither the inner
node's bitmap nor LE-b runs at it. So putinv's `UpLebFitsOK` holds at every
state where the fill holds, vacuously (`upLebFitsOKL_of`).

The path's flags: along the key access path from the space root through live
klongs, every node is reached with the walk's flags (`fReach_path`); the
child of an inner node is reached as no segment tree's root.
-/
import SIS.Tree.LiveCounts
import SIS.Tree.DelStepsLebFull

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- Every node of a path from r through live klongs is reached with some
flags. -/
theorem fReach_path (N : NodeId → Option KNode) (t : Time) (r : NodeId)
    (X : Nat → NodeId) (Nn : Nat → KNode) (K : Nat → Nat) (depth : Nat) (hX0 : X 0 = r)
    (hN : ∀ i, i ≤ depth → N (X i) = some (Nn i))
    (hlink : ∀ i, 0 < i → i ≤ depth → (K i, X i) ∈ (Nn (i - 1)).liveAt t) :
    ∀ i, i ≤ depth → ∃ b s, FReach N t r (X i) b s := by
  intro i
  induction i with
  | zero => intro _; exact ⟨true, true, by rw [hX0]; exact FReach.root⟩
  | succ i ih =>
    intro hi
    obtain ⟨b, s, hr⟩ := ih (by omega)
    have hl := hlink (i + 1) (by omega) hi
    simp only [Nat.add_sub_cancel] at hl
    cases hleaf : (Nn i).leaf with
    | false => exact ⟨false, s, FReach.inner _ b s (Nn i) _ _ hr (hN i (by omega)) hleaf hl⟩
    | true => exact ⟨true, false, FReach.seg _ b s (Nn i) _ _ hr (hN i (by omega)) hleaf hl⟩

/-- A node whose live klongs a delete of compare value k removes all has at
most one live klong. -/
theorem liveAt_length_le_one_of_allKeysIn (n : KNode) (t : Time) (k : Nat)
    (ht : ∀ s, Klong.time s ∈ n.ks → s ≤ t)
    (h : n.allKeysIn (bitsUnion n.lastBitmap (n.bitsOf k)) = true) : (n.liveAt t).length ≤ 1 := by
  rw [KNode.liveAt_of_times n t ht]
  have hk : ∀ q ∈ n.live, q.1 = k := fun q hq => allKeysIn_live_cv n k h q.1 q.2 hq
  have hnd := KNode.live_keys_nodup n
  match hl : n.live with
  | [] => simp
  | [_] => simp
  | q1 :: q2 :: rest =>
    exfalso
    rw [hl] at hnd
    have e1 := hk q1 (by rw [hl]; simp)
    have e2 := hk q2 (by rw [hl]; simp)
    simp only [List.map_cons, List.nodup_cons, List.mem_cons, List.mem_map] at hnd
    exact hnd.1 (Or.inl (by rw [e1, e2]))

/-- With the merges on and the fill: below an inner node of the path, no node
that a delete of compare value k empties. -/
theorem stopLeaf_of_liveCounts (p : Params) (N : NodeId → Option KNode) (t : Time) (r : NodeId)
    (hL : LiveCounts p N t r) (hm : p.merges = true)
    (X : Nat → NodeId) (Nn : Nat → KNode) (K : Nat → Nat) (depth : Nat) (hX0 : X 0 = r)
    (hN : ∀ i, i ≤ depth → N (X i) = some (Nn i))
    (hlink : ∀ i, 0 < i → i ≤ depth → (K i, X i) ∈ (Nn (i - 1)).liveAt t)
    (j : Nat) (hj : j + 1 ≤ depth) (hinner : (Nn j).leaf = false) (k : Nat)
    (ht : ∀ s, Klong.time s ∈ (Nn (j + 1)).ks → s ≤ t)
    (hempty : (Nn (j + 1)).allKeysIn (bitsUnion (Nn (j + 1)).lastBitmap ((Nn (j + 1)).bitsOf k)) = true) :
    False := by
  obtain ⟨b, s, hr⟩ := fReach_path N t r X Nn K depth hX0 hN hlink j (by omega)
  have hl := hlink (j + 1) (by omega) hj
  simp only [Nat.add_sub_cancel] at hl
  have hr1 := FReach.inner _ b s (Nn j) _ _ hr (hN j (by omega)) hinner hl
  have h3 := (hL _ false s (Nn (j + 1)) hr1 (hN (j + 1) hj)).2.2 hm rfl
  have h1 := liveAt_length_le_one_of_allKeysIn (Nn (j + 1)) t k ht hempty
  have h2 : 2 ≤ p.mergeBelow := by unfold Params.merges at hm; simpa using hm
  omega

/-- putinv's `UpLebFitsOK` with the fill at the delete's start and the merges
on. -/
def UpLebFitsOKL (c : Ctx) (base : View BVal) (KO : KindOracle) (BK : NodeId) : Prop :=
  ∀ (w w3 : W) (B MB : NodeId) (top0 : Top) (pre : List Nat) (cv : Nat) (rk : NodeId)
    (X : Nat → NodeId) (Nn : Nat → KNode) (K : Nat → Nat) (depth stop : Nat) (w2 : W) (S : KNode),
    c.p.merges = true → LiveCounts c.p (wNode c.p base w) c.i w.top.rootKey →
    2 ≤ c.p.splitAbove → ViewIdsBelow BK c.view → ViewKinds KO BK c → ICEFromKinds c base KO BK →
    X 0 = w.top.rootKey → PutBase c base B →
    PutInv c base w → RangeOrder (wNode c.p base w) c.i w.top.rootKey →
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
    UpLoopEnd c MB X Nn depth stop w3 w2 S → KdJP c B top0 KO BK w3.path w2 →
    (Nn stop).leaf = false → K (stop + 1) = 0 → S.smallestLive = some 0 →
    ∀ (compact : Bool) (s : String) (t : Klong) (c1 : Nat) (y1 : NodeId) (r : List Klong),
    (S.lastVersionGivenDel c.i (bitsUnion S.lastBitmap (S.bitsOf 0))).ks = t :: .key c1 y1 :: r →
    WriterWP (handleFull stop (X stop)
      { S.lastVersionGivenDel c.i (bitsUnion S.lastBitmap (S.bitsOf 0)) with ks := t :: .key 0 y1 :: r } compact)
      c ({ w2 with trail := s :: w2.trail } : W)
      (fun _ w' => SegFits (wNode c.p base w') c.i c.p.fuel w'.top.rootKey)

/-- `UpLebFitsOKL` holds: with the merges on and the fill at the delete's
start, LE-b never runs at the stop node (its node is inner, and the node
below it on the path is emptied). -/
theorem upLebFitsOKL_of (c : Ctx) (base : View BVal) (KO : KindOracle) (BK : NodeId) :
    UpLebFitsOKL c base KO BK := by
  intro w w3 B MB top0 pre cv rk X Nn K depth stop w2 S hm hL _ _ _ _ hX0 _ hI _ _ _ _ _ _ _ _ _ _
    hwN hlink _ hall _ _ hsd hbetween _ _ hinner _ _
  exfalso
  have ht : ∀ i, i ≤ depth → ∀ s, Klong.time s ∈ (Nn i).ks → s ≤ c.i :=
    fun i hi => hI.times _ _ (hwN i hi)
  by_cases hd : stop + 1 = depth
  · subst hd
    exact stopLeaf_of_liveCounts c.p _ c.i _ hL hm X Nn K (stop + 1) hX0 hwN hlink stop
      (Nat.le_refl _) hinner cv (ht _ (Nat.le_refl _)) hall
  · exact stopLeaf_of_liveCounts c.p _ c.i _ hL hm X Nn K depth hX0 hwN hlink stop (by omega)
      hinner (K (stop + 1 + 1)) (ht _ (by omega)) (hbetween (stop + 1) (by omega) (by omega))

end SIS.Tree
