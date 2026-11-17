/-
The full stop node below the space root that the transaction made, split in time in
place (bergdb 030-01, step 6): the stop node's node becomes its last version without the
chain's klong (`writerWP_handleFullWith_timeInPlace_nodesL`), which has the live klongs
the stop node's bitmap would leave. So the hole is the stop node, as with room: the live
frame (`liveEdgesH_up`) and R1 at the stop node (`holeAtW_stop`, with the key's path
read from the walk's start), the segments from the kinds after the split
(`kd_handleFull`). The heights after any split of the stop node below the root come from
the upward walk's start through the swap (`writerWP_upCasc_below_ht`).
`upCascSplitRestOK_of_rest2` narrows the obligation to its other cases
(`UpCascSplitRest2OK`). The made stop node split in space in place leaves no hole
(`writerWP_upCasc_below_madeSpaceH`, l4b's in-place lemmas at the swapped state), and
`upCascSplitRest2OK_of_rest3` narrows it further (`UpCascSplitRest3OK`: a stop node not
made split in time, the copy the hole; a made space root).
-/
import SIS.Tree.LiveUpCascBelow

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- A path read entry by entry is linked. -/
theorem linkedFrom_of_nodes (N : NodeId → Option KNode) (t : Time) :
    ∀ (steps : List (Option Nat × NodeId)) (x : NodeId),
      (∀ i, i < steps.length → ∃ k n, steps[i]? = some (some k, nodeAt x steps (i + 1)) ∧
        N (nodeAt x steps i) = some n ∧ (k, nodeAt x steps (i + 1)) ∈ n.liveAt t) →
      LinkedFrom N t x steps := by
  intro steps
  induction steps with
  | nil => intro x _; exact LinkedFrom.nil x
  | cons e rest ih =>
    intro x h
    obtain ⟨k, n, h1, h2, h3⟩ := h 0 (by simp)
    have he : e = (some k, e.2) := by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h1
      rw [h1]
    have hn1 : nodeAt x (e :: rest) 1 = e.2 := by simp [nodeAt]
    have hn0 : nodeAt x (e :: rest) 0 = x := by simp [nodeAt]
    rw [hn1] at h3
    rw [hn0] at h2
    rw [he]
    refine LinkedFrom.cons x n k e.2 rest h2 h3 (ih e.2 ?_)
    intro i hi
    obtain ⟨k', n', h1', h2', h3'⟩ := h (i + 1) (by simp; omega)
    have hs1 : nodeAt x (e :: rest) (i + 1 + 1) = nodeAt e.2 rest (i + 1) := by simp [nodeAt]
    have hs0 : nodeAt x (e :: rest) (i + 1) = nodeAt e.2 rest i := by simp [nodeAt]
    rw [hs1] at h1' h3'
    rw [hs0] at h2'
    simp only [List.getElem?_cons_succ] at h1'
    exact ⟨k', n', h1', h2', h3'⟩

set_option maxHeartbeats 12800000 in
/-- The full stop node X (D + 1) below the space root, made by the transaction, split
in time in place: after the split the live counts hold but at the stop node, which the
merges' descent at its pair (g, 0) finds. -/
theorem writerWP_upCasc_below_madeTime (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (hsa2 : 2 ≤ c.p.splitAbove) (KO : KindOracle) (B : NodeId) (hvB : ViewIdsBelow B c.view)
    (hk : ViewKinds KO B c) (hB : PutBase c base B)
    (w w3 : W) (top0 : Top) (pre : List Nat) (cv : Nat) (rk : NodeId)
    (X : Nat → NodeId) (Nn : Nat → KNode) (K : Nat → Nat) (depth D : Nat) (w2 : W) (S : KNode) (g : Nat)
    (hI : PutInv c base w) (hr03 : ReadsAs c.p base w w3)
    (hLC : LiveCounts c.p (wNode c.p base w) c.i w.top.rootKey)
    (hlen3 : w3.path.length = depth + 1) (hX0 : X 0 = w.top.rootKey)
    (hkey : keyWf (pre ++ [cv]) = true)
    (hrk : segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk)
    (hvis : (X depth, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk)
    (hpX : ∀ i, i ≤ depth → (w3.path[i]?).map (·.2) = some (X i))
    (hpK : ∀ i, 0 < i → i ≤ depth → w3.path[i]? = some (some (K i), X i))
    (hlkX : ∀ i, i ≤ depth → w3.nodes.lookup (X i) = some (Nn i))
    (hXN : ∀ i, i ≤ depth → wNode c.p base w (X i) = some (Nn i))
    (hlinkK : ∀ i, 0 < i → i ≤ depth → (K i, X i) ∈ (Nn (i - 1)).liveAt c.i)
    (hleaf : (Nn depth).leaf = true) (hsD : D + 1 < depth)
    (hstp : (Nn (D + 1)).allKeysIn (bitsUnion (Nn (D + 1)).lastBitmap ((Nn (D + 1)).bitsOf (K (D + 1 + 1)))) = true →
      D + 1 = 0 ∧ (Nn 0).leaf = true)
    (hLE : UpLoopEnd c B X Nn depth (D + 1) w3 w2 S) (hJw2 : KdJP c B top0 KO B w3.path w2)
    (hsl : (Nn (D + 1)).leaf = true) (hmade : (Nn (D + 1)).firstTime = some c.i)
    (hlook : w2.gh.lookup (X (D + 1)) = some (g, 0))
    (compact : Bool) (s : String)
    (htime : (!compact && decide ((S.lastVersionGivenDel c.i
      (bitsUnion S.lastBitmap (S.bitsOf (K (D + 1 + 1))))).size > c.p.splitAbove)) = false) :
    WriterWP (handleFull (D + 1) (X (D + 1))
        (S.lastVersionGivenDel c.i (bitsUnion S.lastBitmap (S.bitsOf (K (D + 1 + 1))))) compact) c
      ({ ({ w2 with trail := "up.stop-at-segment-leaf" :: w2.trail } : W) with
        trail := s :: ({ w2 with trail := "up.stop-at-segment-leaf" :: w2.trail } : W).trail } : W)
      (fun _ w' => LiveHoleW (pre ++ [cv]) g 0 c base w') := by
  have hT := hI.tree
  have hN3 : ∀ i, i ≤ depth → wNode c.p base w3 (X i) = some (Nn i) := fun i hi => by
    rw [hr03.1]; exact hXN i hi
  have hPL : ∀ i, i ≤ depth → PathLen (wNode c.p base w) c.i w.top.rootKey (X i) i := by
    intro i
    induction i with
    | zero => intro _; rw [hX0]; exact PathLen.root
    | succ i ih =>
      intro hi
      exact PathLen.link (ih (by omega)) ⟨Nn i, hXN i (by omega), by
        have := hlinkK (i + 1) (by omega) hi; simpa using this⟩
  have hreach : ∀ i, i ≤ depth → TReach (wNode c.p base w) c.i w.top.rootKey (X i) :=
    fun i hi => (hPL i hi).reach
  have hdist : ∀ i i', i ≤ depth → i' ≤ depth → X i = X i' → i = i' := by
    intro i i' h1 h2 he
    have a := hPL i h1
    have b := hPL i' h2
    rw [he] at a
    exact PathLen.depth_unique hT _ _ _ a b
  have htk3 : ∀ i, i ≤ depth → w3.taken.contains (X i) = false := fun i hi => by
    rw [hr03.2.2.1]; exact hI.untaken _ (tReach_reachS _ _ _ _ (hreach i hi))
  have hT3 : TreeOK (wNode c.p base w3) c.i w3.top.rootKey := by rw [hr03.1, hr03.2.1]; exact hT
  have hreach3 : ∀ i, i ≤ depth → TReach (wNode c.p base w3) c.i w3.top.rootKey (X i) := fun i hi => by
    rw [hr03.1, hr03.2.1]; exact hreach i hi
  have hE3 : LiveEdges c.p (wNode c.p base w3) c.i w3.top.rootKey := by
    rw [hr03.1, hr03.2.1]; exact edges_of_liveCounts c.p _ _ _ hLC
  obtain ⟨h2t, h2top, _, h2p, _, _, h2n, hSl, hS, _, _, _, _⟩ := hLE
  have hXs : ∀ k, D + 1 < k → k ≤ depth → X (D + 1) ≠ X k :=
    fun k h1 h2 he => by have := hdist (D + 1) k (by omega) h2 he; omega
  -- the stop node at the loop's end
  have hst_t : ∀ s', Klong.time s' ∈ (Nn (D + 1)).ks → s' ≤ c.i := hI.times _ _ (hXN (D + 1) (by omega))
  have hsx : (K (D + 1 + 1), X (D + 1 + 1)) ∈ (Nn (D + 1)).liveAt c.i := by
    have := hlinkK (D + 1 + 1) (by omega) (by omega); simpa using this
  have hswf : klongsWf (Nn (D + 1)).ks = true := hI.wf _ _ (hXN (D + 1) (by omega))
  have hu : ∀ c', (c', X (D + 1 + 1)) ∈ (Nn (D + 1)).liveAt c.i → c' = K (D + 1 + 1) := by
    intro c' h
    exact (hT.oneLink _ _ _ _ _ (hreach (D + 1) (by omega)) (hreach (D + 1) (by omega))
      ⟨_, hXN (D + 1) (by omega), h⟩ ⟨_, hXN (D + 1) (by omega), hsx⟩).2
  have hSf : S.shapeOf = (Nn (D + 1)).shapeOf ∧ S.leaf = (Nn (D + 1)).leaf ∧
      (∀ s, Klong.time s ∈ S.ks → s ≤ c.i) ∧
      ∀ c' z, ((c', z) ∈ S.liveAt c.i ∧ c' ≠ K (D + 1 + 1)) ↔
        ((c', z) ∈ (Nn (D + 1)).liveAt c.i ∧ c' ≠ K (D + 1 + 1)) := by
    rcases hS with rfl | ⟨ti, dst, rfl⟩
    · exact ⟨rfl, rfl, hst_t, fun _ _ => Iff.rfl⟩
    · exact ⟨KNode.retarget_shapeOf _ _ _ _, rfl, KNode.retarget_times _ _ _ _ _ hst_t,
        KNode.retarget_liveAt_ne _ _ _ _ _ _ hu⟩
  obtain ⟨hSsh, hSleaf, hSt, hSlive⟩ := hSf
  have hSmade : S.firstTime = some c.i := by rw [KNode.firstTime_of_shapeOf hSsh]; exact hmade
  -- the state after the note
  generalize hv4 : ({ ({ w2 with trail := "up.stop-at-segment-leaf" :: w2.trail } : W) with
    trail := s :: ({ w2 with trail := "up.stop-at-segment-leaf" :: w2.trail } : W).trail } : W) = v4
  have h4n : v4.nodes = w2.nodes := by rw [← hv4]
  have h4t : v4.taken = w2.taken := by rw [← hv4]
  have h4top : v4.top = w2.top := by rw [← hv4]
  have h4gh : v4.gh = w2.gh := by rw [← hv4]
  have h4p : v4.path = w3.path := by rw [← hv4]; exact h2p
  have hJv4 : KdJP c B top0 KO B w3.path v4 := by
    rw [← hv4]
    exact kdJP_note c base B top0 hB KO B hvB hk _ s _
      (kdJP_note c base B top0 hB KO B hvB hk _ "up.stop-at-segment-leaf" w2 hJw2)
  have hlk4 : v4.nodes.lookup (X (D + 1)) = some S := by rw [h4n]; exact hSl
  have hx4 : (X (D + 1), g, 0) ∈ v4.gh := by rw [h4gh]; exact upf_mem_of_lookup _ _ _ hlook
  have hpx4 : v4.path[D + 1]? = some (some (K (D + 1)), X (D + 1)) := by
    rw [h4p]; exact hpK (D + 1) (by omega) (by omega)
  have hord := KNode.lastVersionGivenDel_order S c.i (bitsUnion S.lastBitmap (S.bitsOf (K (D + 1 + 1))))
  have hkdS : kdKs (KindKlong KO v4 g 0)
      (S.lastVersionGivenDel c.i (bitsUnion S.lastBitmap (S.bitsOf (K (D + 1 + 1))))).ks :=
    kdKs_lastVersionGivenDel c.i _ (kd_cache_at hlk4 hJv4.1.2.2 hx4 (KdLe.refl v4))
  generalize hlast : S.lastVersionGivenDel c.i (bitsUnion S.lastBitmap (S.bitsOf (K (D + 1 + 1)))) = last
    at htime hord hkdS ⊢
  obtain ⟨hleq, hlwf, hlt, _, _, _, hiff, _⟩ := delLast_split_facts c S (K (D + 1 + 1)) hsa2 hSt last hlast
  have hliveL : ∀ c' z, (c', z) ∈ (⟨S.leaf, last.ks⟩ : KNode).liveAt c.i ↔
      (c', z) ∈ (Nn (D + 1)).liveAt c.i ∧ c' ≠ K (D + 1 + 1) := by
    intro c' z; rw [hleq, hiff c' z]; exact hSlive c' z
  -- the split in place, and the kinds after it
  have hN := writerWP_handleFullWith_timeInPlace_nodesL (fun q more => appendKlongs D q more) (D + 1) (X (D + 1))
    S last compact c v4 hlk4 hSmade htime (by
      intro e q he hq
      have he' : e = D := by omega
      subst he'
      have h := hpX e (by omega)
      rw [← h4p, hq] at h
      simp only [Option.some.injEq] at h
      subst h
      have hne : X e ≠ X (e + 1) := fun hx => by have := hdist e (e + 1) (by omega) (by omega) hx; omega
      refine ⟨Nn e, ?_⟩
      rw [h4n, h2n (X e) hne (fun k h1 h2 hx => by have := hdist e k (by omega) h2 hx; omega)]
      exact hlkX e (by omega))
  have hKd := kd_handleFull KO B (D + 1) (X (D + 1)) last compact c v4 hvB hk hJv4.1.2.1 hJv4.1.2.2 g 0 hx4
    ⟨_, hpx4⟩ hkdS
  refine writerWP_mono (writerWP_and hN hKd) ?_
  rintro _ wf ⟨⟨hfn, hft, hftop, hfgh, _⟩, hfb, hfi, _, _⟩
  -- the stop node after: its last version
  have hfx : wf.nodes.lookup (X (D + 1)) = some ⟨S.leaf, last.ks⟩ := by
    rw [hfn, lookup_upsert]; simp
  have hfo : ∀ y, y ≠ X (D + 1) → (∀ k, D + 1 < k → k ≤ depth → y ≠ X k) →
      wf.nodes.lookup y = w3.nodes.lookup y := by
    intro y h1 h2
    rw [hfn, lookup_upsert]
    simp only [h1, ↓reduceIte]
    rw [h4n, h2n y h1 h2]
  have htkf : wf.taken.contains (X (D + 1)) = false := by
    rw [hft, h4t, h2t _ hXs]; exact htk3 (D + 1) (by omega)
  have hsnF : wNode c.p base wf (X (D + 1)) = some ⟨S.leaf, last.ks⟩ := by
    simp only [wNode, htkf, Bool.false_eq_true, ↓reduceIte, hfx]
  have hagreeF : ∀ u, u ≠ X (D + 1) → (∀ i, D + 1 < i → i ≤ depth → u ≠ X i) →
      wNode c.p base wf u = wNode c.p base w3 u := by
    intro u h1 h2
    simp only [wNode, hft, h4t, h2t u h2, hfo u h1 h2]
  have hkeep : (Nn (D + 1)).allKeysIn (bitsUnion (Nn (D + 1)).lastBitmap
      ((Nn (D + 1)).bitsOf (K (D + 1 + 1)))) = false := by
    cases h : (Nn (D + 1)).allKeysIn (bitsUnion (Nn (D + 1)).lastBitmap
        ((Nn (D + 1)).bitsOf (K (D + 1 + 1)))) with
    | false => rfl
    | true => exact absurd (hstp h).1 (by omega)
  obtain ⟨c1, z1, hc1, hz1⟩ := exists_live_of_keep _ _ hkeep
  have hposF : (⟨S.leaf, last.ks⟩ : KNode).liveAt c.i ≠ [] := by
    intro h0
    have : (c1, z1) ∈ (⟨S.leaf, last.ks⟩ : KNode).liveAt c.i :=
      (hliveL c1 z1).mpr ⟨by rw [KNode.liveAt_of_times _ c.i hst_t]; exact hz1, hc1⟩
    rw [h0] at this
    cases this
  have hrootF : wf.top.rootKey = w3.top.rootKey := by rw [hftop, h4top, h2top]
  have hE : LiveEdgesH c.p (wNode c.p base wf) c.i wf.top.rootKey (fun y => y = X (D + 1)) := by
    rw [hrootF]
    exact liveEdgesH_up c.p (wNode c.p base w3) (wNode c.p base wf) c.i w3.top.rootKey X Nn K (D + 1) depth
      hsD hT3 (hreach3 (D + 1) (by omega)) (fun i _ hi => hN3 i hi) (fun i h1 hi => hlinkK i (by omega) hi)
      (fun i i' _ hi _ hi' he => hdist i i' hi hi' he) hagreeF _ hsnF hSleaf
      (fun c' z h => (hliveL c' z).mp h) hposF hE3
  -- R1 at the stop node, the key's path read from the walk's start
  refine liveHoleW_of_hole (pre ++ [cv]) g 0 c base wf (X (D + 1)) hE ?_
  obtain ⟨e0, rest, hpe⟩ : ∃ e0 rest, w3.path = e0 :: rest := by
    cases h : w3.path with
    | nil => rw [h] at hlen3; simp at hlen3
    | cons e0 rest => exact ⟨e0, rest, rfl⟩
  have hPl : rest.length = depth := by rw [hpe] at hlen3; simpa using hlen3
  have hnA : ∀ i, i ≤ depth → nodeAt w.top.rootKey rest i = X i := by
    intro i hi
    cases i with
    | zero => simp [nodeAt, hX0]
    | succ j =>
      have h := hpX (j + 1) hi
      rw [hpe] at h
      simp only [List.getElem?_cons_succ] at h
      simp only [nodeAt, List.getElem?_cons_succ, List.getElem?_map]
      rw [Option.map_eq_some_iff] at h
      obtain ⟨e, he, he2⟩ := h
      rw [he]; simp [he2]
  have hlinkP : LinkedFrom (wNode c.p base w) c.i w.top.rootKey rest := by
    refine linkedFrom_of_nodes _ c.i rest w.top.rootKey (fun i hi => ?_)
    rw [hPl] at hi
    have h := hpK (i + 1) (by omega) (by omega)
    rw [hpe] at h
    simp only [List.getElem?_cons_succ] at h
    refine ⟨K (i + 1), Nn i, by rw [hnA (i + 1) (by omega)]; exact h, by rw [hnA i (by omega)]; exact hXN i (by omega),
      by rw [hnA (i + 1) (by omega)]; have := hlinkK (i + 1) (by omega) (by omega); simpa using this⟩
  have hXD : nodeAt w.top.rootKey rest rest.length = X depth := by rw [hPl]; exact hnA depth (Nat.le_refl _)
  have hD1 : nodeAt w.top.rootKey rest (D + 1) = X (D + 1) := hnA (D + 1) (by omega)
  have hlkX' : ∀ i, i ≤ rest.length → ({ w3 with path := (none, w.top.rootKey) :: rest } : W).nodes.lookup
      (nodeAt w.top.rootKey rest i) = some ((wNode c.p base w (nodeAt w.top.rootKey rest i)).getD (Nn depth)) := by
    intro i hi
    rw [hPl] at hi
    rw [hnA i hi, hXN i hi]
    exact hlkX i hi
  have hcut : ∀ z, (((rest[D + 1]?).bind (·.1)).getD 0, z) ∉ (⟨S.leaf, last.ks⟩ : KNode).live := by
    intro z hz
    have h := hpK (D + 1 + 1) (by omega) (by omega)
    rw [hpe] at h
    simp only [List.getElem?_cons_succ] at h
    rw [h] at hz
    simp only [Option.bind_some, Option.getD_some] at hz
    rw [← KNode.liveAt_of_times (⟨S.leaf, last.ks⟩ : KNode) c.i hlt] at hz
    exact ((hliveL _ z).mp hz).2 rfl
  have hgL : rdG c wf (nodeAt w.top.rootKey rest (D + 1)) = some (g, 0) := by
    rw [hD1, rdG_of_lookup c wf _ _ hfx, hfgh, h4gh]; exact hlook
  have hH := holeAtW_stop c base hvc w ({ w3 with path := (none, w.top.rootKey) :: rest } : W) wf pre cv rk
    (X depth) (Nn depth) rest (D + 1) g ⟨S.leaf, last.ks⟩ hT
    (fun y hy => hI.untaken y (tReach_reachS _ _ _ _ hy)) hI.wf hrk hvis (hXN depth (Nat.le_refl _)) hleaf
    ⟨hr03.1, hr03.2.1, hr03.2.2.1, hr03.2.2.2.1, hr03.2.2.2.2⟩ rfl hlinkP hXD hlkX' hkey (by omega)
    (by rw [hD1, hXN (D + 1) (by omega)]; exact hsl)
    (by
      intro y h1 h2
      rw [hD1] at h1
      exact hfo y h1 (fun k hk1 hk2 hy => h2 k hk1 (by omega) (by rw [hnA k (by omega)]; exact hy)))
    (by rw [hftop, h4top, h2top])
    (by rw [hD1]; exact hfx) (by rw [hSleaf]; exact hsl) hcut hlwf hlt (segRd_of KO B c wf hfb hfi hk) hgL
  rw [hD1] at hH
  exact hH

set_option maxHeartbeats 12800000 in
/-- The heights after the split of the full stop node X (D + 1) below the space root,
whatever the split: at the state whose stop node has its bitmap (S') they come from the
upward walk's start (`htInv_upFrame`), and the split's heights' walk (`ht_handleFull`)
keeps them; moved by the swap. -/
theorem writerWP_upCasc_below_ht (c : Ctx) (base : View BVal)
    (hsa2 : 2 ≤ c.p.splitAbove) (B : NodeId) (hpos : 0 < c.i)
    (w w3 : W) (X : Nat → NodeId) (Nn : Nat → KNode) (K : Nat → Nat) (depth D : Nat) (w2 v : W) (S : KNode)
    (hI : PutInv c base w)
    (hRO : RangeOrder (wNode c.p base w) c.i w.top.rootKey)
    (hr03 : ReadsAs c.p base w w3)
    (hpX : ∀ i, i ≤ depth → (w3.path[i]?).map (·.2) = some (X i))
    (hpK : ∀ i, 0 < i → i ≤ depth → w3.path[i]? = some (some (K i), X i))
    (hlkX : ∀ i, i ≤ depth → w3.nodes.lookup (X i) = some (Nn i))
    (hXN : ∀ i, i ≤ depth → wNode c.p base w (X i) = some (Nn i))
    (hlinkK : ∀ i, 0 < i → i ≤ depth → (K i, X i) ∈ (Nn (i - 1)).liveAt c.i)
    (hsD : D + 1 < depth)
    (hX0 : X 0 = w.top.rootKey)
    (hLE : UpLoopEnd c B X Nn depth (D + 1) w3 w2 S)
    (hv : v = w2 ∨ ∃ s, v = { w2 with trail := s :: w2.trail })
    (hsl : (Nn (D + 1)).leaf = true)
    (hcu : CacheUnique v)
    (hlinks2 : ∀ u c' z, TLink (wNode c.p base w2) c.i u c' z → z < w2.next)
    (hwf2 : ∀ z zn, wNode c.p base w2 z = some zn → klongsWf zn.ks = true)
    {H : NodeId → Nat → Prop} (hvo : ViewHtOK H B c) (hb3 : Book B c w3) (hi3 : HtInv H B c w3)
    (hkw3 : WriterKlongsWf w3) (hJ3 : TakeJ2 c base B w3) (hbv : Book B c v) (hghv : v.gh = w3.gh)
    (hpathv : v.path = w3.path)
    (compact : Bool) (s : String) :
    WriterWP (handleFull (D + 1) (X (D + 1))
        (S.lastVersionGivenDel c.i (bitsUnion S.lastBitmap (S.bitsOf (K (D + 1 + 1))))) compact) c
      ({ v with trail := s :: v.trail } : W)
      (fun _ w' => HtInv H B c w') := by
  have hfuel : 1 ≤ c.p.fuel := by unfold Params.fuel; omega
  have hT := hI.tree
  have hdepth : 0 < depth := by omega
  -- the path at w and at w3
  have hN3 : ∀ i, i ≤ depth → wNode c.p base w3 (X i) = some (Nn i) := fun i hi => by
    rw [hr03.1]; exact hXN i hi
  have hPL : ∀ i, i ≤ depth → PathLen (wNode c.p base w) c.i w.top.rootKey (X i) i := by
    intro i
    induction i with
    | zero => intro _; rw [hX0]; exact PathLen.root
    | succ i ih =>
      intro hi
      exact PathLen.link (ih (by omega)) ⟨Nn i, hXN i (by omega), by
        have := hlinkK (i + 1) (by omega) hi; simpa using this⟩
  have hreach : ∀ i, i ≤ depth → TReach (wNode c.p base w) c.i w.top.rootKey (X i) :=
    fun i hi => (hPL i hi).reach
  have hdist : ∀ i i', i ≤ depth → i' ≤ depth → X i = X i' → i = i' := by
    intro i i' h1 h2 he
    have a := hPL i h1
    have b := hPL i' h2
    rw [he] at a
    exact PathLen.depth_unique hT _ _ _ a b
  have hI3 := putInv_of_readsAs c base w w3 hI hr03
  have htk3 : ∀ i, i ≤ depth → w3.taken.contains (X i) = false := fun i hi => by
    rw [hr03.2.2.1]; exact hI.untaken _ (tReach_reachS _ _ _ _ (hreach i hi))
  have hT3 : TreeOK (wNode c.p base w3) c.i w3.top.rootKey := by rw [hr03.1, hr03.2.1]; exact hT
  have hR3 : RangeOrder (wNode c.p base w3) c.i w3.top.rootKey := by rw [hr03.1, hr03.2.1]; exact hRO
  have hreach3 : ∀ i, i ≤ depth → TReach (wNode c.p base w3) c.i w3.top.rootKey (X i) := fun i hi => by
    rw [hr03.1, hr03.2.1]; exact hreach i hi
  have hwf3 : ∀ x xn, TReach (wNode c.p base w3) c.i w3.top.rootKey x → wNode c.p base w3 x = some xn →
      klongsWf xn.ks = true := fun x xn _ h => by rw [hr03.1] at h; exact hI.wf x xn h
  have hnoval3 : ∀ i, i ≤ depth → wValue base w3 (X i) = none := fun i hi => by
    rw [ReadsAs.value _ _ _ _ hr03]; exact hI.keyNoValue _ _ (hXN i hi)
  -- the chain's facts at w3 from its order
  have hP3 : PathOK c w3 depth X K Nn :=
    ⟨hpX, hpK, fun i hi => ⟨hlkX i hi, htk3 i hi⟩, hlinkK, by rw [hr03.2.1, hX0]⟩
  have hO := ordG_of_rangeOrder c _ _ hR3 (fun x n h => hI3.times x n h)
  have hwX : ∀ j, j ≤ depth → wNode c.p base w3 (X j) = some (Nn j) := hN3
  -- the loop's end
  obtain ⟨h2t, h2top, h2v, _, _, h2nx, h2n, hSl, hS, hSR, hSF', hfate2, hfateJ2⟩ := hLE
  have hvn : v.nodes = w2.nodes := by rcases hv with rfl | ⟨s, rfl⟩ <;> rfl
  have hvt : v.taken = w2.taken := by rcases hv with rfl | ⟨s, rfl⟩ <;> rfl
  have hvtop : v.top = w2.top := by rcases hv with rfl | ⟨s, rfl⟩ <;> rfl
  have hvv : v.vals = w2.vals := by rcases hv with rfl | ⟨s, rfl⟩ <;> rfl
  have hvnx : v.next = w2.next := by rcases hv with rfl | ⟨s, rfl⟩ <;> rfl
  have hvp : v.path = w3.path := hpathv
  have hwv : wNode c.p base v = wNode c.p base w2 := by
    funext z; simp only [wNode, hvn, hvt]
  -- the stop node now
  have hXs : ∀ k, D + 1 < k → k ≤ depth → X (D + 1) ≠ X k :=
    fun k h1 h2 he => by have := hdist (D + 1) k (by omega) h2 he; omega
  have hst_t : ∀ s', Klong.time s' ∈ (Nn (D + 1)).ks → s' ≤ c.i := hI.times _ _ (hXN (D + 1) (by omega))
  have hsx : (K (D + 1 + 1), X (D + 1 + 1)) ∈ (Nn (D + 1)).liveAt c.i := by
    have := hlinkK (D + 1 + 1) (by omega) (by omega); simpa using this
  have hneS : bitsUnion (Nn (D + 1)).lastBitmap ((Nn (D + 1)).bitsOf (K (D + 1 + 1))) ≠
      (Nn (D + 1)).lastBitmap := by
    apply KNode.delete_bitmap_changes_of_live
    have hsx' := hsx
    rw [KNode.liveAt_of_times _ c.i hst_t] at hsx'
    exact List.mem_map.mpr ⟨_, hsx', rfl⟩
  have hswf : klongsWf (Nn (D + 1)).ks = true := hI.wf _ _ (hXN (D + 1) (by omega))
  have hu : ∀ c', (c', X (D + 1 + 1)) ∈ (Nn (D + 1)).liveAt c.i → c' = K (D + 1 + 1) := by
    intro c' h
    exact (hT.oneLink _ _ _ _ _ (hreach (D + 1) (by omega)) (hreach (D + 1) (by omega))
      ⟨_, hXN (D + 1) (by omega), h⟩ ⟨_, hXN (D + 1) (by omega), hsx⟩).2
  have hSf : S.shapeOf = (Nn (D + 1)).shapeOf ∧ S.leaf = (Nn (D + 1)).leaf ∧ klongsWf S.ks = true ∧
      (∀ s, Klong.time s ∈ S.ks → s ≤ c.i) ∧
      ∀ c' z, ((c', z) ∈ S.liveAt c.i ∧ c' ≠ K (D + 1 + 1)) ↔
        ((c', z) ∈ (Nn (D + 1)).liveAt c.i ∧ c' ≠ K (D + 1 + 1)) := by
    rcases hS with rfl | ⟨ti, dst, rfl⟩
    · exact ⟨rfl, rfl, hswf, hst_t, fun _ _ => Iff.rfl⟩
    · exact ⟨KNode.retarget_shapeOf _ _ _ _, rfl, by rw [klongsWf_retargetKlongs]; exact hswf,
        KNode.retarget_times _ _ _ _ _ hst_t, KNode.retarget_liveAt_ne _ _ _ _ _ _ hu⟩
  obtain ⟨hSsh, hSleaf, hSwf, hSt, hSlive⟩ := hSf
  have hneS' : bitsUnion S.lastBitmap (S.bitsOf (K (D + 1 + 1))) ≠ S.lastBitmap := by
    rw [KNode.lastBitmap_of_shapeOf hSsh, KNode.bitsOf_of_shapeOf hSsh]; exact hneS
  have hlkv : v.nodes.lookup (X (D + 1)) = some S := by rw [hvn]; exact hSl
  have htk2 : w2.taken.contains (X (D + 1)) = false := by rw [h2t _ hXs]; exact htk3 (D + 1) (by omega)
  have hagree2 : ∀ u, u ≠ X (D + 1) → (∀ i, D + 1 < i → i ≤ depth → u ≠ X i) →
      wNode c.p base w2 u = wNode c.p base w3 u := fun u hus hnc => by
    simp only [wNode, h2t u hnc, h2n u hus hnc]
  -- the chain above the stop node, unchanged
  have hXne : ∀ i, i ≤ D → ∀ k, D + 1 ≤ k → k ≤ depth → X i ≠ X k :=
    fun i hi k h1 h2 he => by have := hdist i k (by omega) h2 he; omega
  have hlk2 : ∀ i, i ≤ D → w2.nodes.lookup (X i) = some (Nn i) := fun i hi => by
    rw [h2n (X i) (hXne i hi (D + 1) (Nat.le_refl _) (by omega))
      (fun k h1 h2 => hXne i hi k (by omega) h2)]
    exact hlkX i (by omega)
  have htk2' : ∀ i, i ≤ D → w2.taken.contains (X i) = false := fun i hi => by
    rw [h2t (X i) (fun k h1 h2 => hXne i hi k (by omega) h2)]; exact htk3 i (by omega)
  -- the stop node with its bitmap as if it had room (S')
  generalize hS'd : S.add c.i (.del (bitsUnion S.lastBitmap (S.bitsOf (K (D + 1 + 1))))) = S'
  have hbm : BitmapOf S S' c.i (K (D + 1 + 1)) := Or.inl hS'd.symm
  have hS'leaf : S'.leaf = S.leaf := bitmapOf_leaf S S' c.i _ hbm
  have hS'wf : klongsWf S'.ks = true := by rw [← hS'd]; exact KNode.add_delete_wf S c.i _ hSwf hneS'
  have hS't : ∀ s, Klong.time s ∈ S'.ks → s ≤ c.i := by
    rw [← hS'd]; exact KNode.add_times S c.i _ (fun s h => by cases h) hSt
  have hS'live : ∀ c' z, (c', z) ∈ S'.liveAt c.i ↔
      (c', z) ∈ (Nn (D + 1)).liveAt c.i ∧ c' ≠ K (D + 1 + 1) := by
    intro c' z
    rw [liveAt_iff_of_delete_lookup S S' c.i _ hSt hS't
      (fun c' => by rw [← hS'd]; exact S.add_delete_live_lookup c.i _ c')]
    exact hSlive c' z
  obtain ⟨s0, hs0, hs0m⟩ := KNode.firstTime_some_of_live (Nn (D + 1)) c.i hswf _ _ hsx
  have hs0S : S.firstTime = some s0 := by rw [KNode.firstTime_of_shapeOf hSsh]; exact hs0
  have hft : S.firstTime = S'.firstTime := by rw [hs0S, bitmapOf_firstTime S S' c.i _ hbm s0 hs0S]
  have hprev : S'.firstTime ≠ some c.i → S.toPrev (c.i - 1) = S'.toPrev (c.i - 1) := by
    intro hne
    have hpos : 0 < c.i := by
      rcases Nat.eq_zero_or_pos c.i with h0 | h0
      · exfalso
        have hle := hst_t s0 hs0m
        apply hne
        rw [← hft, hs0S, show s0 = c.i by omega]
      · exact h0
    show (⟨S.leaf, prefixAt S.ks (c.i - 1)⟩ : KNode) = ⟨S'.leaf, prefixAt S'.ks (c.i - 1)⟩
    rw [hS'leaf, bitmapOf_prefix S S' c.i _ hbm hpos]
  -- the chain with the stop node's node with its bitmap
  generalize hNn' : (fun i => if i = D + 1 then S' else Nn i) = Nn'
  have hNn'S : Nn' (D + 1) = S' := by rw [← hNn']; simp
  have hNn'i : ∀ i, i ≤ D → Nn' i = Nn i := fun i hi => by
    rw [← hNn']; simp only [show i ≠ D + 1 by omega, ↓reduceIte]
  have hCO : ∀ i, 0 < i → i ≤ D → ChainOrd c K Nn' i := by
    intro i h1 h2
    have h := chainOrd_of_ordG c base w3 depth X K Nn hP3 hO i h1 (by omega)
    unfold ChainOrd at h ⊢
    rw [hNn'i i h2, hNn'i (i - 1) (by omega)]
    exact h
  have hflat := KNode.lastVersionGivenDel_flatAt S c.i (bitsUnion S.lastBitmap (S.bitsOf (K (D + 1 + 1))))
  have hord := KNode.lastVersionGivenDel_order S c.i (bitsUnion S.lastBitmap (S.bitsOf (K (D + 1 + 1))))
  generalize hlast : S.lastVersionGivenDel c.i (bitsUnion S.lastBitmap (S.bitsOf (K (D + 1 + 1)))) = last
    at hflat hord ⊢
  obtain ⟨hleq, hlwf, hlt, hlastV, hlen2, _, hiff, _⟩ :=
    delLast_split_facts c S (K (D + 1 + 1)) hsa2 hSt last hlast
  have hliveL : ∀ c' z, (c', z) ∈ (⟨S.leaf, last.ks⟩ : KNode).liveAt c.i ↔
      (c', z) ∈ (Nn (D + 1)).liveAt c.i ∧ c' ≠ K (D + 1 + 1) := by
    intro c' z; rw [hleq, hiff c' z]; exact hSlive c' z
  have hlk' : ({ v with trail := s :: v.trail } : W).nodes.lookup (X (D + 1)) = some S := hlkv
  have hroot' : ({ v with trail := s :: v.trail } : W).top.rootKey = w3.top.rootKey := by
    show v.top.rootKey = _; rw [hvtop, h2top]
  have hnx' : ({ v with trail := s :: v.trail } : W).next = w3.next := by
    show v.next = _; rw [hvnx, h2nx]
  have hwv' : wNode c.p base ({ v with trail := s :: v.trail } : W) = wNode c.p base w2 := hwv
  have hXlt : ∀ i, i ≤ depth → X i < w3.next := fun i hi => hI3.ids.1 (X i) (by rw [hlkX i hi]; rfl)
  have hS5 : ∀ z, ({ v with trail := s :: v.trail } : W).next ≤ z →
      ({ v with trail := s :: v.trail } : W).nodes.lookup z = none ∧
      ({ v with trail := s :: v.trail } : W).taken.contains z = false ∧ knodeOf c.p base z = none := by
    intro z hz
    rw [hnx'] at hz
    have hzX : ∀ i, i ≤ depth → z ≠ X i := fun i hi he => by have := hXlt i hi; omega
    refine ⟨?_, ?_, (hI.fresh z (by rw [← hr03.2.2.2.2]; exact hz)).1⟩
    · show v.nodes.lookup z = none
      rw [hvn, h2n z (hzX (D + 1) (by omega)) (fun i _ hi => hzX i hi)]
      cases h' : w3.nodes.lookup z with
      | none => rfl
      | some _ => have := hI3.ids.1 z (by rw [h']; rfl); omega
    · show v.taken.contains z = false
      rw [hvt, h2t z (fun i _ hi => hzX i hi)]
      cases h' : w3.taken.contains z with
      | false => rfl
      | true => have := hI3.ids.2.2.1 z h'; omega
  have hS6 : ∀ u c' z, TLink (wNode c.p base ({ v with trail := s :: v.trail } : W)) c.i u c' z →
      z < ({ v with trail := s :: v.trail } : W).next := by
    rw [hwv']; intro u c' z hl
    show z < v.next
    rw [hvnx]; exact hlinks2 u c' z hl
  have hW : ∀ z zn, wNode c.p base ({ v with trail := s :: v.trail } : W) z = some zn →
      klongsWf zn.ks = true := by
    rw [hwv']; exact hwf2
  have htkv : ({ v with trail := s :: v.trail } : W).taken.contains (X (D + 1)) = false := by
    show v.taken.contains _ = false; rw [hvt]; exact htk2
  -- the split moved from the state with S' to the writer's (the swap)
  have hswap : ∀ (post : Unit → W → Prop),
      WriterWP (handleFull (D + 1) (X (D + 1)) last compact) c
        (setX (X (D + 1)) S' ({ v with trail := s :: v.trail } : W)) post →
      WriterWP (handleFull (D + 1) (X (D + 1)) last compact) c ({ v with trail := s :: v.trail } : W) post := by
    intro post h
    have h2 := writerWP_handleFull_swap (X (D + 1)) S' S (D + 1) last compact c _ post (lookup_setX_self _ _ _)
      (by show X (D + 1) < v.next; rw [hvnx, h2nx]; exact hXlt (D + 1) (by omega))
      (by
        intro i e hi he
        have hp := hpX i (by omega)
        rw [← hvp] at hp
        change v.path[i]? = some e at he
        rw [he] at hp
        simp only [Option.map_some, Option.some.injEq] at hp
        rw [hp]
        intro hx
        have := hdist i (D + 1) (by omega) (by omega) hx
        omega)
      hft hS'leaf.symm hprev h
    rwa [setX_setX, setX_self _ _ _ (show CacheUnique ({ v with trail := s :: v.trail } : W) from hcu) hlk']
      at h2
  refine hswap _ ?_
  generalize hud : setX (X (D + 1)) S' ({ v with trail := s :: v.trail } : W) = u
  have hu_top : u.top = ({ v with trail := s :: v.trail } : W).top := by rw [← hud]; rfl
  have hu_next : u.next = ({ v with trail := s :: v.trail } : W).next := by rw [← hud]; rfl
  have hu_taken : u.taken = ({ v with trail := s :: v.trail } : W).taken := by rw [← hud]; rfl
  have hu_vals : u.vals = ({ v with trail := s :: v.trail } : W).vals := by rw [← hud]; rfl
  have hu_path : u.path = w3.path := by rw [← hud]; exact hvp
  have hwu : wNode c.p base u =
      updN (wNode c.p base ({ v with trail := s :: v.trail } : W)) (X (D + 1)) S' := by
    rw [← hud]; exact wNode_upsert_updN c.p base _ _ (X (D + 1)) S' rfl rfl htkv
  have hsnu : wNode c.p base u (X (D + 1)) = some S' := by rw [hwu]; exact updN_self _ _ _
  have hagreeU : ∀ u0, u0 ≠ X (D + 1) → (∀ i, D + 1 < i → i ≤ depth → u0 ≠ X i) →
      updN (wNode c.p base ({ v with trail := s :: v.trail } : W)) (X (D + 1)) S' u0 =
        wNode c.p base w3 u0 := fun u0 hus hnc => by
    rw [updN_ne _ _ _ _ hus, hwv']; exact hagree2 u0 hus hnc
  have hS2' : ∀ i, 0 ≤ i → i ≤ D + 1 →
      u.nodes.lookup (X i) = some (Nn' i) ∧ u.taken.contains (X i) = false := by
    intro i _ hi
    rcases Nat.lt_or_ge i (D + 1) with h | h
    · rw [hNn'i i (by omega), hu_taken]
      have hne : X i ≠ X (D + 1) := fun he => by
        have := hdist i (D + 1) (by omega) (by omega) he; omega
      refine ⟨?_, by show v.taken.contains _ = false; rw [hvt]; exact htk2' i (by omega)⟩
      rw [← hud]
      have := hlk2 i (by omega)
      simpa [setX, lookup_upsert, hne, hvn] using this
    · have hi' : i = D + 1 := by omega
      subst hi'
      rw [hNn'S, hu_taken]
      exact ⟨by rw [← hud]; exact lookup_setX_self _ _ _, htkv⟩
  have hT2' : TreeOK (wNode c.p base u) c.i u.top.rootKey := by
    rw [hu_top, hroot', hwu]
    exact treeOK_up_tr (wNode c.p base w3) _ c.i w3.top.rootKey X Nn K (D + 1) depth hsD hT3
      (hreach3 (D + 1) (by omega)) (fun i _ hi => hN3 i hi) (fun i h1 hi => hlinkK i (by omega) hi)
      (fun i i' _ hi _ hi' he => hdist i i' hi hi' he) hagreeU _ (updN_self _ _ _) id
      (fun c' z h => ⟨c', ((hS'live c' z).mp h).1, ((hS'live c' z).mp h).2, rfl⟩)
  have hS4' : ∀ i, 0 ≤ i → i ≤ D + 1 → TReach (wNode c.p base u) c.i u.top.rootKey (X i) := by
    intro i _ hi
    rw [hwu, hu_top, hroot']
    induction i with
    | zero => rw [hr03.2.1, hX0]; exact TReach.root
    | succ i ih =>
      have hi' : i ≤ D := by omega
      have hne : X i ≠ X (D + 1) := fun he => by
        have := hdist i (D + 1) (by omega) (by omega) he; omega
      refine TReach.link (ih (Nat.zero_le _) (by omega)) ⟨Nn i, ?_, by
        have := hlinkK (i + 1) (by omega) (by omega); simpa using this⟩
      rw [updN_ne _ _ _ _ hne, hwv']
      simp only [wNode, htk2' i hi', Bool.false_eq_true, ↓reduceIte, hlk2 i hi']
  have hS5u : ∀ z, u.next ≤ z → u.nodes.lookup z = none ∧ u.taken.contains z = false ∧
      knodeOf c.p base z = none := by
    intro z hz
    rw [hu_next] at hz
    obtain ⟨h1, h2, h3⟩ := hS5 z hz
    have hz0 : z ≠ X (D + 1) := fun he => by
      have := hXlt (D + 1) (by omega); rw [← hnx'] at this; omega
    refine ⟨?_, by rw [hu_taken]; exact h2, h3⟩
    rw [← hud]; simp only [setX, lookup_upsert, hz0, ↓reduceIte]; exact h1
  have hS6u : ∀ a c' z, TLink (wNode c.p base u) c.i a c' z → z < u.next := by
    intro a c' z ⟨an, han, hl⟩
    rw [hu_next]
    by_cases ha : a = X (D + 1)
    · rw [ha, hsnu] at han; cases han
      rw [hnx', hr03.2.2.2.2]
      exact hI.links (X (D + 1)) (Nn (D + 1)) c' z (tReach_reachS _ _ _ _ (hreach (D + 1) (by omega)))
        (hXN (D + 1) (by omega)) ((hS'live c' z).mp hl).1
    · rw [hwu, updN_ne _ _ _ _ ha] at han
      exact hS6 a c' z ⟨an, han, hl⟩
  have hWu : ∀ z zn, wNode c.p base u z = some zn → klongsWf zn.ks = true := by
    intro z zn hz
    by_cases hz0 : z = X (D + 1)
    · rw [hz0, hsnu] at hz; cases hz; exact hS'wf
    · rw [hwu, updN_ne _ _ _ _ hz0] at hz; exact hW z zn hz
  have hpath' : u.path = w3.path := hu_path
  -- the heights at u: the walk's start's, through the loop's frame
  have hlku : u.nodes.lookup (X (D + 1)) = some S' := by rw [← hud]; exact lookup_setX_self _ _ _
  have htku : u.taken.contains (X (D + 1)) = false := (hS2' (D + 1) (Nat.zero_le _) (Nat.le_refl _)).2
  have hbu : Book B c u := by
    have hbv' : Book B c ({ v with trail := s :: v.trail } : W) :=
      ⟨hbv.next, hbv.ids, hbv.bound, hbv.nodup, hbv.leaf, hbv.tag, hbv.taken, hbv.top⟩
    have h := book_putNode B (X (D + 1)) S' c ({ v with trail := s :: v.trail } : W) hbv' ⟨S, hlk', hS'leaf⟩
    exact (h () u (by rw [← hud]; rfl)).1
  have hghu : u.gh = w3.gh := by rw [← hud]; exact hghv
  have htu : ∀ y, (∀ k, D + 1 < k → k ≤ depth → y ≠ X k) → u.taken.contains y = w3.taken.contains y := by
    intro y hy
    rw [hu_taken]; show v.taken.contains y = _; rw [hvt]; exact h2t y hy
  have htopu : u.top = w3.top := by rw [hu_top]; show v.top = _; rw [hvtop]; exact h2top
  have hnodesu : ∀ y, y ≠ X (D + 1) → (∀ k, D + 1 < k → k ≤ depth → y ≠ X k) →
      u.nodes.lookup y = w3.nodes.lookup y := by
    intro y h1 h2
    rw [← hud]; simp only [setX, lookup_upsert, h1, ↓reduceIte]
    show v.nodes.lookup y = _; rw [hvn]; exact h2n y h1 h2
  have hfJu : ∀ k, D + 1 < k → k ≤ depth → ChainFateW c.i B u (Nn k) (X k) := by
    intro k h1 h2
    refine chainFateW_frame c.i B w2 u (Nn k) (X k) (hfateJ2 k h1 h2) ?_ ?_
    · rw [hu_taken]; show v.taken = _; exact hvt
    · rw [← hud]; simp only [setX, lookup_upsert, Ne.symm (hXs k h1 h2), ↓reduceIte]
      show v.nodes.lookup _ = _; rw [hvn]
  have hX03 : X 0 = w3.top.rootKey := by rw [hr03.2.1, hX0]
  have hiu : HtInv H B c u :=
    htInv_upFrame B c base w3 u X Nn K depth (D + 1) hpos hb3 hi3 hkw3 hbu (fun e he => by rw [hghu]; exact he)
      hu_path hJ3 hT3 (fun q qn hq s' hs' => by rw [hr03.1] at hq; exact hI.times q qn hq s' hs') hsD hX03 hlkX
      htk3 hdist hreach3 hlinkK htu htopu hnodesu S' hlku hS't hS'live hfJu ⟨S, hSR, hbm⟩
  obtain ⟨g0, h0, hm0⟩ := kd_tag_of_lookup hb3 (hlkX (D + 1) (by omega))
  have hh0 : h0 = 0 := kd_h0 hb3 (hlkX (D + 1) (by omega)) hm0 hsl
  subst hh0
  have hxu : (X (D + 1), g0, 0) ∈ u.gh := by rw [hghu]; exact hm0
  have hpxu : u.path[D + 1]? = some (some (K (D + 1)), X (D + 1)) := by
    rw [hu_path]; exact hpK (D + 1) (by omega) (by omega)
  have hpf : PathFreeTo u (D + 1 + 1) := by
    intro d a' q hd hq
    have h := hpX d (by omega)
    rw [← hu_path, hq] at h
    simp only [Option.map_some, Option.some.injEq] at h
    rw [h]
    exact (hS2' d (Nat.zero_le _) (by omega)).2
  have hNu : NodeHt c H u 0 S' := ht_cache_at hlku hiu hxu htku (HtLe.refl u)
  have hlastK : kdKs (HtP c H u 0) last.ks := by
    intro c' y hm
    have hl0 := ht_flat_live hord hm
    have hl1 : (c', y) ∈ (⟨S.leaf, last.ks⟩ : KNode).liveAt c.i := by
      rw [hleq, KNode.liveAt_of_times _ c.i hlt]; exact hl0
    have hl2 := (hS'live c' y).mpr ((hliveL c' y).mp hl1)
    rw [KNode.liveAt_of_times _ c.i hS't] at hl2
    exact ⟨(hNu.live c' y hl2).1, fun h => absurd rfl h⟩
  have hHt : WriterWP (handleFull (D + 1) (X (D + 1)) last compact) c u (fun _ w' => HtInv H B c w') :=
    writerWP_mono (ht_handleFull B (D + 1) (X (D + 1)) last compact c u hvo hpos hbu hiu g0 0 hxu
      (some (K (D + 1))) hpxu hpf hflat hlastK) (fun _ _ h => h.2.1)
  exact hHt



set_option maxHeartbeats 12800000 in
/-- The full stop node X (D + 1) below the space root, made by the transaction, split
in space in place with no compaction: after the split the heights hold and the live
counts hold with no hole (l4b's `writerWP_handleFull_spaceInPlaceChain_live` below an
inner parent, `writerWP_handleFull_segSpaceMade_live` below a segment leaf). -/
theorem writerWP_upCasc_below_madeSpaceH (c : Ctx) (base : View BVal)
    (hsa2 : 2 ≤ c.p.splitAbove) (hp : MergeParamsOK c.p) (B : NodeId) (hpos : 0 < c.i)
    (w w3 : W) (X : Nat → NodeId) (Nn : Nat → KNode) (K : Nat → Nat) (depth D : Nat) (w2 v : W) (S : KNode)
    (hI : PutInv c base w)
    (hRO : RangeOrder (wNode c.p base w) c.i w.top.rootKey)
    (hr03 : ReadsAs c.p base w w3)
    (hLC : LiveCounts c.p (wNode c.p base w) c.i w.top.rootKey)
    (hpX : ∀ i, i ≤ depth → (w3.path[i]?).map (·.2) = some (X i))
    (hpK : ∀ i, 0 < i → i ≤ depth → w3.path[i]? = some (some (K i), X i))
    (hlkX : ∀ i, i ≤ depth → w3.nodes.lookup (X i) = some (Nn i))
    (hXN : ∀ i, i ≤ depth → wNode c.p base w (X i) = some (Nn i))
    (hlinkK : ∀ i, 0 < i → i ≤ depth → (K i, X i) ∈ (Nn (i - 1)).liveAt c.i)
    (hsD : D + 1 < depth)
    (hX0 : X 0 = w.top.rootKey)
    (hLE : UpLoopEnd c B X Nn depth (D + 1) w3 w2 S)
    (hv : v = w2 ∨ ∃ s, v = { w2 with trail := s :: w2.trail })
    (hsl : (Nn (D + 1)).leaf = true) (hmade : (Nn (D + 1)).firstTime = some c.i)
    (hcu : CacheUnique v)
    (hlinks2 : ∀ u c' z, TLink (wNode c.p base w2) c.i u c' z → z < w2.next)
    (hwf2 : ∀ z zn, wNode c.p base w2 z = some zn → klongsWf zn.ks = true)
    {H : NodeId → Nat → Prop} (hvo : ViewHtOK H B c) (hb3 : Book B c w3) (hi3 : HtInv H B c w3)
    (hkw3 : WriterKlongsWf w3) (hJ3 : TakeJ2 c base B w3) (hbv : Book B c v) (hghv : v.gh = w3.gh)
    (hpathv : v.path = w3.path)
    (compact : Bool) (hc : compact = false) (s : String)
    (hsp : c.p.splitAbove <
      (S.lastVersionGivenDel c.i (bitsUnion S.lastBitmap (S.bitsOf (K (D + 1 + 1))))).size) :
    WriterWP (handleFull (D + 1) (X (D + 1))
        (S.lastVersionGivenDel c.i (bitsUnion S.lastBitmap (S.bitsOf (K (D + 1 + 1))))) compact) c
      ({ v with trail := s :: v.trail } : W)
      (fun _ w' => HtInv H B c w' ∧ LiveEdges c.p (wNode c.p base w') c.i w'.top.rootKey) := by
  have hfuel : 1 ≤ c.p.fuel := by unfold Params.fuel; omega
  have hT := hI.tree
  have hdepth : 0 < depth := by omega
  -- the path at w and at w3
  have hN3 : ∀ i, i ≤ depth → wNode c.p base w3 (X i) = some (Nn i) := fun i hi => by
    rw [hr03.1]; exact hXN i hi
  have hPL : ∀ i, i ≤ depth → PathLen (wNode c.p base w) c.i w.top.rootKey (X i) i := by
    intro i
    induction i with
    | zero => intro _; rw [hX0]; exact PathLen.root
    | succ i ih =>
      intro hi
      exact PathLen.link (ih (by omega)) ⟨Nn i, hXN i (by omega), by
        have := hlinkK (i + 1) (by omega) hi; simpa using this⟩
  have hreach : ∀ i, i ≤ depth → TReach (wNode c.p base w) c.i w.top.rootKey (X i) :=
    fun i hi => (hPL i hi).reach
  have hdist : ∀ i i', i ≤ depth → i' ≤ depth → X i = X i' → i = i' := by
    intro i i' h1 h2 he
    have a := hPL i h1
    have b := hPL i' h2
    rw [he] at a
    exact PathLen.depth_unique hT _ _ _ a b
  have hI3 := putInv_of_readsAs c base w w3 hI hr03
  have htk3 : ∀ i, i ≤ depth → w3.taken.contains (X i) = false := fun i hi => by
    rw [hr03.2.2.1]; exact hI.untaken _ (tReach_reachS _ _ _ _ (hreach i hi))
  have hT3 : TreeOK (wNode c.p base w3) c.i w3.top.rootKey := by rw [hr03.1, hr03.2.1]; exact hT
  have hR3 : RangeOrder (wNode c.p base w3) c.i w3.top.rootKey := by rw [hr03.1, hr03.2.1]; exact hRO
  have hreach3 : ∀ i, i ≤ depth → TReach (wNode c.p base w3) c.i w3.top.rootKey (X i) := fun i hi => by
    rw [hr03.1, hr03.2.1]; exact hreach i hi
  have hwf3 : ∀ x xn, TReach (wNode c.p base w3) c.i w3.top.rootKey x → wNode c.p base w3 x = some xn →
      klongsWf xn.ks = true := fun x xn _ h => by rw [hr03.1] at h; exact hI.wf x xn h
  have hnoval3 : ∀ i, i ≤ depth → wValue base w3 (X i) = none := fun i hi => by
    rw [ReadsAs.value _ _ _ _ hr03]; exact hI.keyNoValue _ _ (hXN i hi)
  -- the chain's facts at w3 from its order
  have hP3 : PathOK c w3 depth X K Nn :=
    ⟨hpX, hpK, fun i hi => ⟨hlkX i hi, htk3 i hi⟩, hlinkK, by rw [hr03.2.1, hX0]⟩
  have hO := ordG_of_rangeOrder c _ _ hR3 (fun x n h => hI3.times x n h)
  have hwX : ∀ j, j ≤ depth → wNode c.p base w3 (X j) = some (Nn j) := hN3
  -- the loop's end
  obtain ⟨h2t, h2top, h2v, _, _, h2nx, h2n, hSl, hS, hSR, hSF', hfate2, hfateJ2⟩ := hLE
  have hvn : v.nodes = w2.nodes := by rcases hv with rfl | ⟨s, rfl⟩ <;> rfl
  have hvt : v.taken = w2.taken := by rcases hv with rfl | ⟨s, rfl⟩ <;> rfl
  have hvtop : v.top = w2.top := by rcases hv with rfl | ⟨s, rfl⟩ <;> rfl
  have hvv : v.vals = w2.vals := by rcases hv with rfl | ⟨s, rfl⟩ <;> rfl
  have hvnx : v.next = w2.next := by rcases hv with rfl | ⟨s, rfl⟩ <;> rfl
  have hvp : v.path = w3.path := hpathv
  have hwv : wNode c.p base v = wNode c.p base w2 := by
    funext z; simp only [wNode, hvn, hvt]
  -- the stop node now
  have hXs : ∀ k, D + 1 < k → k ≤ depth → X (D + 1) ≠ X k :=
    fun k h1 h2 he => by have := hdist (D + 1) k (by omega) h2 he; omega
  have hst_t : ∀ s', Klong.time s' ∈ (Nn (D + 1)).ks → s' ≤ c.i := hI.times _ _ (hXN (D + 1) (by omega))
  have hsx : (K (D + 1 + 1), X (D + 1 + 1)) ∈ (Nn (D + 1)).liveAt c.i := by
    have := hlinkK (D + 1 + 1) (by omega) (by omega); simpa using this
  have hneS : bitsUnion (Nn (D + 1)).lastBitmap ((Nn (D + 1)).bitsOf (K (D + 1 + 1))) ≠
      (Nn (D + 1)).lastBitmap := by
    apply KNode.delete_bitmap_changes_of_live
    have hsx' := hsx
    rw [KNode.liveAt_of_times _ c.i hst_t] at hsx'
    exact List.mem_map.mpr ⟨_, hsx', rfl⟩
  have hswf : klongsWf (Nn (D + 1)).ks = true := hI.wf _ _ (hXN (D + 1) (by omega))
  have hu : ∀ c', (c', X (D + 1 + 1)) ∈ (Nn (D + 1)).liveAt c.i → c' = K (D + 1 + 1) := by
    intro c' h
    exact (hT.oneLink _ _ _ _ _ (hreach (D + 1) (by omega)) (hreach (D + 1) (by omega))
      ⟨_, hXN (D + 1) (by omega), h⟩ ⟨_, hXN (D + 1) (by omega), hsx⟩).2
  have hSf : S.shapeOf = (Nn (D + 1)).shapeOf ∧ S.leaf = (Nn (D + 1)).leaf ∧ klongsWf S.ks = true ∧
      (∀ s, Klong.time s ∈ S.ks → s ≤ c.i) ∧
      ∀ c' z, ((c', z) ∈ S.liveAt c.i ∧ c' ≠ K (D + 1 + 1)) ↔
        ((c', z) ∈ (Nn (D + 1)).liveAt c.i ∧ c' ≠ K (D + 1 + 1)) := by
    rcases hS with rfl | ⟨ti, dst, rfl⟩
    · exact ⟨rfl, rfl, hswf, hst_t, fun _ _ => Iff.rfl⟩
    · exact ⟨KNode.retarget_shapeOf _ _ _ _, rfl, by rw [klongsWf_retargetKlongs]; exact hswf,
        KNode.retarget_times _ _ _ _ _ hst_t, KNode.retarget_liveAt_ne _ _ _ _ _ _ hu⟩
  obtain ⟨hSsh, hSleaf, hSwf, hSt, hSlive⟩ := hSf
  have hneS' : bitsUnion S.lastBitmap (S.bitsOf (K (D + 1 + 1))) ≠ S.lastBitmap := by
    rw [KNode.lastBitmap_of_shapeOf hSsh, KNode.bitsOf_of_shapeOf hSsh]; exact hneS
  have hlkv : v.nodes.lookup (X (D + 1)) = some S := by rw [hvn]; exact hSl
  have htk2 : w2.taken.contains (X (D + 1)) = false := by rw [h2t _ hXs]; exact htk3 (D + 1) (by omega)
  have hagree2 : ∀ u, u ≠ X (D + 1) → (∀ i, D + 1 < i → i ≤ depth → u ≠ X i) →
      wNode c.p base w2 u = wNode c.p base w3 u := fun u hus hnc => by
    simp only [wNode, h2t u hnc, h2n u hus hnc]
  -- the chain above the stop node, unchanged
  have hXne : ∀ i, i ≤ D → ∀ k, D + 1 ≤ k → k ≤ depth → X i ≠ X k :=
    fun i hi k h1 h2 he => by have := hdist i k (by omega) h2 he; omega
  have hlk2 : ∀ i, i ≤ D → w2.nodes.lookup (X i) = some (Nn i) := fun i hi => by
    rw [h2n (X i) (hXne i hi (D + 1) (Nat.le_refl _) (by omega))
      (fun k h1 h2 => hXne i hi k (by omega) h2)]
    exact hlkX i (by omega)
  have htk2' : ∀ i, i ≤ D → w2.taken.contains (X i) = false := fun i hi => by
    rw [h2t (X i) (fun k h1 h2 => hXne i hi k (by omega) h2)]; exact htk3 i (by omega)
  -- the stop node with its bitmap as if it had room (S')
  generalize hS'd : S.add c.i (.del (bitsUnion S.lastBitmap (S.bitsOf (K (D + 1 + 1))))) = S'
  have hbm : BitmapOf S S' c.i (K (D + 1 + 1)) := Or.inl hS'd.symm
  have hS'leaf : S'.leaf = S.leaf := bitmapOf_leaf S S' c.i _ hbm
  have hS'wf : klongsWf S'.ks = true := by rw [← hS'd]; exact KNode.add_delete_wf S c.i _ hSwf hneS'
  have hS't : ∀ s, Klong.time s ∈ S'.ks → s ≤ c.i := by
    rw [← hS'd]; exact KNode.add_times S c.i _ (fun s h => by cases h) hSt
  have hS'live : ∀ c' z, (c', z) ∈ S'.liveAt c.i ↔
      (c', z) ∈ (Nn (D + 1)).liveAt c.i ∧ c' ≠ K (D + 1 + 1) := by
    intro c' z
    rw [liveAt_iff_of_delete_lookup S S' c.i _ hSt hS't
      (fun c' => by rw [← hS'd]; exact S.add_delete_live_lookup c.i _ c')]
    exact hSlive c' z
  obtain ⟨s0, hs0, hs0m⟩ := KNode.firstTime_some_of_live (Nn (D + 1)) c.i hswf _ _ hsx
  have hs0S : S.firstTime = some s0 := by rw [KNode.firstTime_of_shapeOf hSsh]; exact hs0
  have hft : S.firstTime = S'.firstTime := by rw [hs0S, bitmapOf_firstTime S S' c.i _ hbm s0 hs0S]
  have hprev : S'.firstTime ≠ some c.i → S.toPrev (c.i - 1) = S'.toPrev (c.i - 1) := by
    intro hne
    have hpos : 0 < c.i := by
      rcases Nat.eq_zero_or_pos c.i with h0 | h0
      · exfalso
        have hle := hst_t s0 hs0m
        apply hne
        rw [← hft, hs0S, show s0 = c.i by omega]
      · exact h0
    show (⟨S.leaf, prefixAt S.ks (c.i - 1)⟩ : KNode) = ⟨S'.leaf, prefixAt S'.ks (c.i - 1)⟩
    rw [hS'leaf, bitmapOf_prefix S S' c.i _ hbm hpos]
  -- the chain with the stop node's node with its bitmap
  generalize hNn' : (fun i => if i = D + 1 then S' else Nn i) = Nn'
  have hNn'S : Nn' (D + 1) = S' := by rw [← hNn']; simp
  have hNn'i : ∀ i, i ≤ D → Nn' i = Nn i := fun i hi => by
    rw [← hNn']; simp only [show i ≠ D + 1 by omega, ↓reduceIte]
  have hCO : ∀ i, 0 < i → i ≤ D → ChainOrd c K Nn' i := by
    intro i h1 h2
    have h := chainOrd_of_ordG c base w3 depth X K Nn hP3 hO i h1 (by omega)
    unfold ChainOrd at h ⊢
    rw [hNn'i i h2, hNn'i (i - 1) (by omega)]
    exact h
  have hHO := halves_del_halfOK c.p hp S c.i (bitsUnion S.lastBitmap (S.bitsOf (K (D + 1 + 1))))
  have hflat := KNode.lastVersionGivenDel_flatAt S c.i (bitsUnion S.lastBitmap (S.bitsOf (K (D + 1 + 1))))
  have hord := KNode.lastVersionGivenDel_order S c.i (bitsUnion S.lastBitmap (S.bitsOf (K (D + 1 + 1))))
  generalize hlast : S.lastVersionGivenDel c.i (bitsUnion S.lastBitmap (S.bitsOf (K (D + 1 + 1)))) = last
    at hsp hHO hflat hord ⊢
  obtain ⟨hleq, hlwf, hlt, hlastV, hlen2, _, hiff, _⟩ :=
    delLast_split_facts c S (K (D + 1 + 1)) hsa2 hSt last hlast
  have hliveL : ∀ c' z, (c', z) ∈ (⟨S.leaf, last.ks⟩ : KNode).liveAt c.i ↔
      (c', z) ∈ (Nn (D + 1)).liveAt c.i ∧ c' ≠ K (D + 1 + 1) := by
    intro c' z; rw [hleq, hiff c' z]; exact hSlive c' z
  have hlk' : ({ v with trail := s :: v.trail } : W).nodes.lookup (X (D + 1)) = some S := hlkv
  have hroot' : ({ v with trail := s :: v.trail } : W).top.rootKey = w3.top.rootKey := by
    show v.top.rootKey = _; rw [hvtop, h2top]
  have hnx' : ({ v with trail := s :: v.trail } : W).next = w3.next := by
    show v.next = _; rw [hvnx, h2nx]
  have hwv' : wNode c.p base ({ v with trail := s :: v.trail } : W) = wNode c.p base w2 := hwv
  have hXlt : ∀ i, i ≤ depth → X i < w3.next := fun i hi => hI3.ids.1 (X i) (by rw [hlkX i hi]; rfl)
  have hS5 : ∀ z, ({ v with trail := s :: v.trail } : W).next ≤ z →
      ({ v with trail := s :: v.trail } : W).nodes.lookup z = none ∧
      ({ v with trail := s :: v.trail } : W).taken.contains z = false ∧ knodeOf c.p base z = none := by
    intro z hz
    rw [hnx'] at hz
    have hzX : ∀ i, i ≤ depth → z ≠ X i := fun i hi he => by have := hXlt i hi; omega
    refine ⟨?_, ?_, (hI.fresh z (by rw [← hr03.2.2.2.2]; exact hz)).1⟩
    · show v.nodes.lookup z = none
      rw [hvn, h2n z (hzX (D + 1) (by omega)) (fun i _ hi => hzX i hi)]
      cases h' : w3.nodes.lookup z with
      | none => rfl
      | some _ => have := hI3.ids.1 z (by rw [h']; rfl); omega
    · show v.taken.contains z = false
      rw [hvt, h2t z (fun i _ hi => hzX i hi)]
      cases h' : w3.taken.contains z with
      | false => rfl
      | true => have := hI3.ids.2.2.1 z h'; omega
  have hS6 : ∀ u c' z, TLink (wNode c.p base ({ v with trail := s :: v.trail } : W)) c.i u c' z →
      z < ({ v with trail := s :: v.trail } : W).next := by
    rw [hwv']; intro u c' z hl
    show z < v.next
    rw [hvnx]; exact hlinks2 u c' z hl
  have hW : ∀ z zn, wNode c.p base ({ v with trail := s :: v.trail } : W) z = some zn →
      klongsWf zn.ks = true := by
    rw [hwv']; exact hwf2
  have htkv : ({ v with trail := s :: v.trail } : W).taken.contains (X (D + 1)) = false := by
    show v.taken.contains _ = false; rw [hvt]; exact htk2
  -- the split moved from the state with S' to the writer's (the swap)
  have hswap : ∀ (post : Unit → W → Prop),
      WriterWP (handleFull (D + 1) (X (D + 1)) last compact) c
        (setX (X (D + 1)) S' ({ v with trail := s :: v.trail } : W)) post →
      WriterWP (handleFull (D + 1) (X (D + 1)) last compact) c ({ v with trail := s :: v.trail } : W) post := by
    intro post h
    have h2 := writerWP_handleFull_swap (X (D + 1)) S' S (D + 1) last compact c _ post (lookup_setX_self _ _ _)
      (by show X (D + 1) < v.next; rw [hvnx, h2nx]; exact hXlt (D + 1) (by omega))
      (by
        intro i e hi he
        have hp := hpX i (by omega)
        rw [← hvp] at hp
        change v.path[i]? = some e at he
        rw [he] at hp
        simp only [Option.map_some, Option.some.injEq] at hp
        rw [hp]
        intro hx
        have := hdist i (D + 1) (by omega) (by omega) hx
        omega)
      hft hS'leaf.symm hprev h
    rwa [setX_setX, setX_self _ _ _ (show CacheUnique ({ v with trail := s :: v.trail } : W) from hcu) hlk']
      at h2
  refine hswap _ ?_
  generalize hud : setX (X (D + 1)) S' ({ v with trail := s :: v.trail } : W) = u
  have hu_top : u.top = ({ v with trail := s :: v.trail } : W).top := by rw [← hud]; rfl
  have hu_next : u.next = ({ v with trail := s :: v.trail } : W).next := by rw [← hud]; rfl
  have hu_taken : u.taken = ({ v with trail := s :: v.trail } : W).taken := by rw [← hud]; rfl
  have hu_vals : u.vals = ({ v with trail := s :: v.trail } : W).vals := by rw [← hud]; rfl
  have hu_path : u.path = w3.path := by rw [← hud]; exact hvp
  have hwu : wNode c.p base u =
      updN (wNode c.p base ({ v with trail := s :: v.trail } : W)) (X (D + 1)) S' := by
    rw [← hud]; exact wNode_upsert_updN c.p base _ _ (X (D + 1)) S' rfl rfl htkv
  have hsnu : wNode c.p base u (X (D + 1)) = some S' := by rw [hwu]; exact updN_self _ _ _
  have hagreeU : ∀ u0, u0 ≠ X (D + 1) → (∀ i, D + 1 < i → i ≤ depth → u0 ≠ X i) →
      updN (wNode c.p base ({ v with trail := s :: v.trail } : W)) (X (D + 1)) S' u0 =
        wNode c.p base w3 u0 := fun u0 hus hnc => by
    rw [updN_ne _ _ _ _ hus, hwv']; exact hagree2 u0 hus hnc
  have hS2' : ∀ i, 0 ≤ i → i ≤ D + 1 →
      u.nodes.lookup (X i) = some (Nn' i) ∧ u.taken.contains (X i) = false := by
    intro i _ hi
    rcases Nat.lt_or_ge i (D + 1) with h | h
    · rw [hNn'i i (by omega), hu_taken]
      have hne : X i ≠ X (D + 1) := fun he => by
        have := hdist i (D + 1) (by omega) (by omega) he; omega
      refine ⟨?_, by show v.taken.contains _ = false; rw [hvt]; exact htk2' i (by omega)⟩
      rw [← hud]
      have := hlk2 i (by omega)
      simpa [setX, lookup_upsert, hne, hvn] using this
    · have hi' : i = D + 1 := by omega
      subst hi'
      rw [hNn'S, hu_taken]
      exact ⟨by rw [← hud]; exact lookup_setX_self _ _ _, htkv⟩
  have hT2' : TreeOK (wNode c.p base u) c.i u.top.rootKey := by
    rw [hu_top, hroot', hwu]
    exact treeOK_up_tr (wNode c.p base w3) _ c.i w3.top.rootKey X Nn K (D + 1) depth hsD hT3
      (hreach3 (D + 1) (by omega)) (fun i _ hi => hN3 i hi) (fun i h1 hi => hlinkK i (by omega) hi)
      (fun i i' _ hi _ hi' he => hdist i i' hi hi' he) hagreeU _ (updN_self _ _ _) id
      (fun c' z h => ⟨c', ((hS'live c' z).mp h).1, ((hS'live c' z).mp h).2, rfl⟩)
  have hS4' : ∀ i, 0 ≤ i → i ≤ D + 1 → TReach (wNode c.p base u) c.i u.top.rootKey (X i) := by
    intro i _ hi
    rw [hwu, hu_top, hroot']
    induction i with
    | zero => rw [hr03.2.1, hX0]; exact TReach.root
    | succ i ih =>
      have hi' : i ≤ D := by omega
      have hne : X i ≠ X (D + 1) := fun he => by
        have := hdist i (D + 1) (by omega) (by omega) he; omega
      refine TReach.link (ih (Nat.zero_le _) (by omega)) ⟨Nn i, ?_, by
        have := hlinkK (i + 1) (by omega) (by omega); simpa using this⟩
      rw [updN_ne _ _ _ _ hne, hwv']
      simp only [wNode, htk2' i hi', Bool.false_eq_true, ↓reduceIte, hlk2 i hi']
  have hS5u : ∀ z, u.next ≤ z → u.nodes.lookup z = none ∧ u.taken.contains z = false ∧
      knodeOf c.p base z = none := by
    intro z hz
    rw [hu_next] at hz
    obtain ⟨h1, h2, h3⟩ := hS5 z hz
    have hz0 : z ≠ X (D + 1) := fun he => by
      have := hXlt (D + 1) (by omega); rw [← hnx'] at this; omega
    refine ⟨?_, by rw [hu_taken]; exact h2, h3⟩
    rw [← hud]; simp only [setX, lookup_upsert, hz0, ↓reduceIte]; exact h1
  have hS6u : ∀ a c' z, TLink (wNode c.p base u) c.i a c' z → z < u.next := by
    intro a c' z ⟨an, han, hl⟩
    rw [hu_next]
    by_cases ha : a = X (D + 1)
    · rw [ha, hsnu] at han; cases han
      rw [hnx', hr03.2.2.2.2]
      exact hI.links (X (D + 1)) (Nn (D + 1)) c' z (tReach_reachS _ _ _ _ (hreach (D + 1) (by omega)))
        (hXN (D + 1) (by omega)) ((hS'live c' z).mp hl).1
    · rw [hwu, updN_ne _ _ _ _ ha] at han
      exact hS6 a c' z ⟨an, han, hl⟩
  have hWu : ∀ z zn, wNode c.p base u z = some zn → klongsWf zn.ks = true := by
    intro z zn hz
    by_cases hz0 : z = X (D + 1)
    · rw [hz0, hsnu] at hz; cases hz; exact hS'wf
    · rw [hwu, updN_ne _ _ _ _ hz0] at hz; exact hW z zn hz
  have hpath' : u.path = w3.path := hu_path
  -- the chain's ranges and lengths
  have hrange : ∀ i, 0 < i → i ≤ D → ¬ ChainRoom c (Nn' i) → (Nn' (i - 1)).leaf = false →
      ∀ c' z, (c', z) ∈ (Nn' i).live → 0 < c' →
      K i ≤ c' ∧ ∀ c'' z', (c'', z') ∈ (Nn' (i - 1)).live → K i < c'' → c' < c'' := by
    intro i h1 hi hNR hql' c' z hz hpos
    rw [hNn'i i hi] at hNR hz
    rw [hNn'i (i - 1) (by omega)] at hql' ⊢
    exact rangeG_of_rangeOrder c _ _ hR3 (fun x n h => hI3.times x n h) (X (i - 1)) (Nn (i - 1)) (X i) (Nn i)
      (K i) (hreach3 (i - 1) (by omega)) (hwX (i - 1) (by omega)) hql' (hlinkK i h1 (by omega))
      (hwX i (by omega)) hNR c' z hz hpos
  have hlen : ∀ i, 0 ≤ i → i ≤ D → ¬ ChainRoom c (Nn' i) →
      c.p.splitAbove < ((Nn' i).lastVersion c.i).size → 2 ≤ (Nn' i).live.length := by
    intro i _ hi hNR hsp
    rw [hNn'i i hi] at hNR hsp ⊢
    exact lenG_of_splitAbove c _ _ hsa2 (X i) (Nn i) (hreach3 i (by omega)) (hwX i (by omega)) hNR hsp
  have hwf' : ∀ i, 0 ≤ i → i ≤ D + 1 → klongsWf (Nn' i).ks = true := by
    intro i _ hi
    rcases Nat.lt_or_ge i (D + 1) with h | h
    · rw [hNn'i i (by omega)]; exact hI.wf _ _ (hXN i (by omega))
    · rw [show i = D + 1 by omega, hNn'S]; exact hS'wf
  have htimes' : ∀ i, 0 ≤ i → i ≤ D + 1 → ∀ t, Klong.time t ∈ (Nn' i).ks → t ≤ c.i := by
    intro i _ hi
    rcases Nat.lt_or_ge i (D + 1) with h | h
    · rw [hNn'i i (by omega)]; exact hI.times _ _ (hXN i (by omega))
    · rw [show i = D + 1 by omega, hNn'S]; exact hS't
  have hlinkK' : ∀ i, 0 < i → i ≤ D + 1 → (K i, X i) ∈ (Nn' (i - 1)).liveAt c.i := by
    intro i h1 hi
    rw [hNn'i (i - 1) (by omega)]; exact hlinkK i h1 (by omega)
  have hdist' : ∀ i i', 0 ≤ i → i ≤ D + 1 → 0 ≤ i' → i' ≤ D + 1 → X i = X i' → i = i' :=
    fun i i' _ hi _ hi' he => hdist i i' (by omega) (by omega) he
  -- the stop node's last version under its parent
  have hkl : (K (D + 1), X (D + 1)) ∈ (Nn D).liveAt c.i := by
    have := hlinkK (D + 1) (by omega) (by omega); simpa using this
  have hrangeLn : (Nn D).leaf = false → ∀ c' z, (c', z) ∈ (⟨S.leaf, last.ks⟩ : KNode).live → 0 < c' →
      K (D + 1) ≤ c' ∧ ∀ c'' z', (c'', z') ∈ (Nn D).live → K (D + 1) < c'' → c' < c'' := by
    intro hql c' z hz hpos'
    have hz' : (c', z) ∈ (⟨S.leaf, last.ks⟩ : KNode).liveAt c.i := by
      rw [KNode.liveAt_of_times (⟨S.leaf, last.ks⟩ : KNode) c.i hlt]; exact hz
    have hzn := ((hliveL c' z).mp hz').1
    obtain ⟨hP1, hP2⟩ := mrg_child_range (wNode c.p base w3) c.i w3.top.rootKey hR3 (X D) (Nn D)
      (tReach_reachS _ _ _ _ (hreach3 D (by omega))) (hwX D (by omega)) hql (K (D + 1)) (X (D + 1))
      (Nn (D + 1)) hkl (hwX (D + 1) (by omega))
    refine ⟨?_, ?_⟩
    · rcases Nat.eq_zero_or_pos (K (D + 1)) with hk0 | hk0
      · omega
      · cases hl : (Nn (D + 1)).leaf with
        | true => exact (hP1 c' z hzn).1 hl hk0
        | false =>
          rcases (hP1 c' z hzn).2 hl with h | h
          · omega
          · exact Nat.le_of_lt (h hk0)
    · intro c'' z' hz2 hlt2
      exact hP2 c'' z' (by rw [KNode.liveAt_of_times _ c.i (hI3.times _ _ (hwX D (by omega)))]; exact hz2)
        hlt2 c' z hzn
  -- the halves of the space split
  obtain ⟨r, hdiv, hsc, hrm, hfh, hsh⟩ := halves_facts_nil c.i ⟨S.leaf, last.ks⟩ (hlen2 hsp) hlt
  rw [hlastV] at hdiv hfh hsh
  obtain ⟨hfH, hsH⟩ := hHO hsp
  have hSl1 : S.leaf = true := hSleaf.trans hsl
  -- the stop node with its bitmap is filled: it holds a half's live klongs
  have hS'H : HalfOK c.p c.i S' := by
    have hle : ((halves S.leaf c.i last []).1.liveAt c.i).length ≤ (S'.liveAt c.i).length :=
      liveAt_length_le _ _ c.i (fun c' z h => ⟨z, (hS'live c' z).mpr ((hliveL c' z).mp (hfh c' z h).2)⟩)
    have h2 := hfH.2.1
    refine ⟨fun h0 => ?_, by omega, fun hm => by have := hfH.2.2 hm; omega⟩
    rw [h0] at hle
    simp only [List.length_nil] at hle
    omega
  -- the live counts at u: the start's without the chain, the stop node filled
  have hE3 : LiveEdges c.p (wNode c.p base w3) c.i w3.top.rootKey := by
    rw [hr03.1, hr03.2.1]; exact edges_of_liveCounts c.p _ _ _ hLC
  have hLu : LiveEdges c.p (wNode c.p base u) c.i u.top.rootKey := by
    have hHl := liveEdgesH_up c.p (wNode c.p base w3) (wNode c.p base u) c.i w3.top.rootKey X Nn K (D + 1)
      depth hsD hT3 (hreach3 (D + 1) (by omega)) (fun i _ hi => hN3 i hi) (fun i h1 hi => hlinkK i (by omega) hi)
      (fun i i' _ hi _ hi' he => hdist i i' hi hi' he) (fun u0 h1 h2 => by rw [hwu]; exact hagreeU u0 h1 h2)
      S' hsnu (by rw [hS'leaf, hSleaf]) (fun c' z h => (hS'live c' z).mp h) hS'H.1 hE3
    rw [hu_top, hroot']
    refine liveEdges_of_oneHole c.p _ c.i _ (X (D + 1)) _ hHl (fun y hy => hy) ?_ ?_
    · intro xn _ hxr _
      exfalso
      rw [hr03.2.1, ← hX0] at hxr
      have := hdist (D + 1) 0 (by omega) (by omega) hxr
      omega
    · intro u0 un cc xn _ _ _ hxn _
      rw [hsnu] at hxn
      cases hxn
      exact childOK_half c.p c.i un S' hS'H
  -- the heights at u: the walk's start's, through the loop's frame
  have hlku : u.nodes.lookup (X (D + 1)) = some S' := by rw [← hud]; exact lookup_setX_self _ _ _
  have htku : u.taken.contains (X (D + 1)) = false := (hS2' (D + 1) (Nat.zero_le _) (Nat.le_refl _)).2
  have hbu : Book B c u := by
    have hbv' : Book B c ({ v with trail := s :: v.trail } : W) :=
      ⟨hbv.next, hbv.ids, hbv.bound, hbv.nodup, hbv.leaf, hbv.tag, hbv.taken, hbv.top⟩
    have h := book_putNode B (X (D + 1)) S' c ({ v with trail := s :: v.trail } : W) hbv' ⟨S, hlk', hS'leaf⟩
    exact (h () u (by rw [← hud]; rfl)).1
  have hghu : u.gh = w3.gh := by rw [← hud]; exact hghv
  have htu : ∀ y, (∀ k, D + 1 < k → k ≤ depth → y ≠ X k) → u.taken.contains y = w3.taken.contains y := by
    intro y hy
    rw [hu_taken]; show v.taken.contains y = _; rw [hvt]; exact h2t y hy
  have htopu : u.top = w3.top := by rw [hu_top]; show v.top = _; rw [hvtop]; exact h2top
  have hnodesu : ∀ y, y ≠ X (D + 1) → (∀ k, D + 1 < k → k ≤ depth → y ≠ X k) →
      u.nodes.lookup y = w3.nodes.lookup y := by
    intro y h1 h2
    rw [← hud]; simp only [setX, lookup_upsert, h1, ↓reduceIte]
    show v.nodes.lookup y = _; rw [hvn]; exact h2n y h1 h2
  have hfJu : ∀ k, D + 1 < k → k ≤ depth → ChainFateW c.i B u (Nn k) (X k) := by
    intro k h1 h2
    refine chainFateW_frame c.i B w2 u (Nn k) (X k) (hfateJ2 k h1 h2) ?_ ?_
    · rw [hu_taken]; show v.taken = _; exact hvt
    · rw [← hud]; simp only [setX, lookup_upsert, Ne.symm (hXs k h1 h2), ↓reduceIte]
      show v.nodes.lookup _ = _; rw [hvn]
  have hX03 : X 0 = w3.top.rootKey := by rw [hr03.2.1, hX0]
  have hiu : HtInv H B c u :=
    htInv_upFrame B c base w3 u X Nn K depth (D + 1) hpos hb3 hi3 hkw3 hbu (fun e he => by rw [hghu]; exact he)
      hu_path hJ3 hT3 (fun q qn hq s' hs' => by rw [hr03.1] at hq; exact hI.times q qn hq s' hs') hsD hX03 hlkX
      htk3 hdist hreach3 hlinkK htu htopu hnodesu S' hlku hS't hS'live hfJu ⟨S, hSR, hbm⟩
  obtain ⟨g0, h0, hm0⟩ := kd_tag_of_lookup hb3 (hlkX (D + 1) (by omega))
  have hh0 : h0 = 0 := kd_h0 hb3 (hlkX (D + 1) (by omega)) hm0 hsl
  subst hh0
  have hxu : (X (D + 1), g0, 0) ∈ u.gh := by rw [hghu]; exact hm0
  have hpxu : u.path[D + 1]? = some (some (K (D + 1)), X (D + 1)) := by
    rw [hu_path]; exact hpK (D + 1) (by omega) (by omega)
  have hpf : PathFreeTo u (D + 1 + 1) := by
    intro d a' q hd hq
    have h := hpX d (by omega)
    rw [← hu_path, hq] at h
    simp only [Option.map_some, Option.some.injEq] at h
    rw [h]
    exact (hS2' d (Nat.zero_le _) (by omega)).2
  have hNu : NodeHt c H u 0 S' := ht_cache_at hlku hiu hxu htku (HtLe.refl u)
  have hlastK : kdKs (HtP c H u 0) last.ks := by
    intro c' y hm
    have hl0 := ht_flat_live hord hm
    have hl1 : (c', y) ∈ (⟨S.leaf, last.ks⟩ : KNode).liveAt c.i := by
      rw [hleq, KNode.liveAt_of_times _ c.i hlt]; exact hl0
    have hl2 := (hS'live c' y).mpr ((hliveL c' y).mp hl1)
    rw [KNode.liveAt_of_times _ c.i hS't] at hl2
    exact ⟨(hNu.live c' y hl2).1, fun h => absurd rfl h⟩
  have hHt : WriterWP (handleFull (D + 1) (X (D + 1)) last compact) c u (fun _ w' => HtInv H B c w') :=
    writerWP_mono (ht_handleFull B (D + 1) (X (D + 1)) last compact c u hvo hpos hbu hiu g0 0 hxu
      (some (K (D + 1))) hpxu hpf hflat hlastK) (fun _ _ h => h.2.1)
  -- the split's live counts, by the parent's kind
  have hf' : ∀ c' z, (c', z) ∈ (halves (Nn' (D + 1)).leaf c.i last []).1.liveAt c.i →
      c' < (halves (Nn' (D + 1)).leaf c.i last []).2.2 ∧ (c', z) ∈ (Nn' (D + 1)).liveAt c.i := by
    rw [hNn'S, hS'leaf, hdiv]
    intro c' z h
    exact ⟨(hfh c' z h).1, (hS'live c' z).mpr ((hliveL c' z).mp (hfh c' z h).2)⟩
  have hs' : ∀ c' z, (c', z) ∈ (halves (Nn' (D + 1)).leaf c.i last []).2.1.liveAt c.i →
      ∃ c0, (halves (Nn' (D + 1)).leaf c.i last []).2.2 ≤ c0 ∧
        c' = splitLocalCv (Nn' (D + 1)).leaf (halves (Nn' (D + 1)).leaf c.i last []).2.2 c0 ∧
        (c0, z) ∈ (Nn' (D + 1)).liveAt c.i := by
    rw [hNn'S, hS'leaf, hdiv]
    intro c' z h
    obtain ⟨c0, h1, h2, h3⟩ := hsh c' z h
    exact ⟨c0, h1, h2, (hS'live c0 z).mpr ((hliveL c0 z).mp h3)⟩
  have hfH' : HalfOK c.p c.i (halves (Nn' (D + 1)).leaf c.i last []).1 := by rw [hNn'S, hS'leaf]; exact hfH
  have hsH' : HalfOK c.p c.i (halves (Nn' (D + 1)).leaf c.i last []).2.1 := by rw [hNn'S, hS'leaf]; exact hsH
  have hfirst' : (Nn' (D + 1)).firstTime = some c.i := by
    rw [hNn'S, ← hft, KNode.firstTime_of_shapeOf hSsh]; exact hmade
  have hR0 : u.top.rootKey = X 0 := by rw [hu_top, hroot', hr03.2.1, hX0]
  have hLv : WriterWP (handleFull (D + 1) (X (D + 1)) last compact) c u
      (fun _ w' => LiveEdges c.p (wNode c.p base w') c.i w'.top.rootKey) := by
    subst hc
    show WriterWP (handleFullWith (fun q more => appendKlongs D q more) (D + 1) (X (D + 1)) [] last false) c u _
    cases hql : (Nn D).leaf with
    | false =>
      exact writerWP_handleFull_spaceInPlaceChain_live c base w3.path D X K Nn' last (fun i hi => hpX i (by omega))
        (fun i h1 hi => hpK i h1 (by omega)) hlinkK' hrange hlen (fun i hi => hwf' i (Nat.zero_le _) hi)
        (fun i hi => htimes' i (Nat.zero_le _) hi)
        (fun i i' hi hi' => hdist' i i' (Nat.zero_le _) hi (Nat.zero_le _) hi') hfirst'
        (by rw [hNn'i D (Nat.le_refl _)]; exact hql) hsp hf' hs' hfH' hsH' hp u hu_path
        (fun i hi => hS2' i (Nat.zero_le _) hi) hT2' (fun i hi => hS4' i (Nat.zero_le _) hi) hS5u hS6u hR0 hLu
    | true =>
      have hlqu : u.nodes.lookup (X D) = some (Nn D) := by
        have h := (hS2' D (Nat.zero_le _) (by omega)).1
        rwa [hNn'i D (Nat.le_refl _)] at h
      have hqtu : u.taken.contains (X D) = false := (hS2' D (Nat.zero_le _) (by omega)).2
      have hqx : X D ≠ X (D + 1) := fun he => by have := hdist D (D + 1) (by omega) (by omega) he; omega
      have hxnu : X (D + 1) < u.next := by
        rw [hu_next, hnx']; exact hXlt (D + 1) (by omega)
      have hqnu : X D < u.next := by
        rw [hu_next, hnx']; exact hXlt D (by omega)
      have hpq : (u.path[D]?).map (·.2) = some (X D) := by rw [hu_path]; exact hpX D (by omega)
      have hfree : ∀ z, u.next ≤ z → wNode c.p base u z = none ∧ u.nodes.lookup z = none ∧
          u.taken.contains z = false := by
        intro z hz
        obtain ⟨h1, h2, h3⟩ := hS5u z hz
        refine ⟨?_, h1, h2⟩
        simp only [wNode, h2, Bool.false_eq_true, ↓reduceIte, h1]
        exact h3
      have hmade' : S'.firstTime = some c.i := by rw [← hNn'S]; exact hfirst'
      rw [hNn'S] at hf' hs' hfH' hsH'
      exact writerWP_handleFull_segSpaceMade_live D (X (D + 1)) (X D) S' (Nn D) (K (D + 1)) last c base u
        hlku htku hlqu hqtu hqx hxnu hqnu hmade' hql hsp hpq hpxu (hI.times _ _ (hXN D (by omega))) hkl
        hT2' (hS4' D (Nat.zero_le _) (by omega)) hfree (fun _ _ _ _ hl => hS6u _ _ _ hl)
        (by rw [hS'leaf, hdiv]; exact hsc) hf' hs' hfH' hsH' hLu
  exact writerWP_mono (writerWP_and hHt hLv) (fun _ _ h => h)


/-- The full stop node's cases left after the made stop node's split in time in place
below the root (bergdb 030-01, step 6): a stop node below the root not made by the
transaction split in time (the copy the hole), a made stop node's split in space in
place, and a made space root. -/
def UpCascSplitRest2OK (c : Ctx) (base : View BVal) (KO : KindOracle) (B : NodeId)
    (H : NodeId → Nat → Prop) : Prop :=
  ∀ (w w3 : W) (top0 : Top) (pre : List Nat) (cv : Nat) (rk : NodeId)
    (X : Nat → NodeId) (Nn : Nat → KNode) (K : Nat → Nat) (depth stop : Nat) (w2 : W) (S : KNode)
    (g : Nat) (compact : Bool) (s : String),
    ViewCoherent c base → c.p.merges = true → 2 ≤ c.p.splitAbove → MergeParamsOK c.p →
    ViewIdsBelow B c.view → ViewKinds KO B c → ICEFromKinds c base KO B →
    ViewHtOK H B c → ViewKlongsWf c.p c.view → 0 < c.i →
    PutBase c base B → PutBook c B top0 w → PutInv c base w →
    RangeOrder (wNode c.p base w) c.i w.top.rootKey →
    InnerChildrenExist (wNode c.p base w) c.i w.top.rootKey →
    LiveCounts c.p (wNode c.p base w) c.i w.top.rootKey →
    TakeJ2 c base B w → (∀ x o, w3.madeFor.lookup x = some o → o < B) →
    ReadsAs c.p base w w3 → KdJ c B top0 KO B w3 → HtInv H B c w3 → WriterKlongsWf w3 →
    w3.path.length = depth + 1 → X 0 = w.top.rootKey →
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
    (Nn depth).leaf = true →
    (∀ c' z, (c', z) ∈ (Nn depth).liveAt c.i → wNode c.p base w z = none) →
    0 < depth → stop < depth →
    (∀ i, stop < i → i < depth →
      (Nn i).allKeysIn (bitsUnion (Nn i).lastBitmap ((Nn i).bitsOf (K (i + 1)))) = true) →
    ((Nn stop).allKeysIn (bitsUnion (Nn stop).lastBitmap ((Nn stop).bitsOf (K (stop + 1)))) = true →
      stop = 0 ∧ (Nn 0).leaf = true) →
    UpLoopEnd c B X Nn depth stop w3 w2 S → KdJP c B top0 KO B w3.path w2 → w2.gh = w3.gh →
    (Nn stop).leaf = true → ¬ DelRoom c (K (stop + 1)) S →
    (0 < stop ∨ (Nn 0).firstTime = some c.i) →
    w2.gh.lookup (X stop) = some (g, 0) →
    ¬ (0 < stop ∧ (Nn stop).firstTime ≠ some c.i ∧ compact = false ∧
      c.p.splitAbove < (S.lastVersionGivenDel c.i (bitsUnion S.lastBitmap (S.bitsOf (K (stop + 1))))).size) →
    ¬ (0 < stop ∧ (Nn stop).firstTime = some c.i ∧ (!compact && decide ((S.lastVersionGivenDel c.i
      (bitsUnion S.lastBitmap (S.bitsOf (K (stop + 1))))).size > c.p.splitAbove)) = false) →
    WriterWP (handleFull stop (X stop)
        (S.lastVersionGivenDel c.i (bitsUnion S.lastBitmap (S.bitsOf (K (stop + 1))))) compact) c
      ({ ({ w2 with trail := "up.stop-at-segment-leaf" :: w2.trail } : W) with
        trail := s :: ({ w2 with trail := "up.stop-at-segment-leaf" :: w2.trail } : W).trail } : W)
      (fun _ w' => HtInv H B c w' ∧ LiveHoleW (pre ++ [cv]) g 0 c base w')

set_option maxHeartbeats 3200000 in
/-- `UpCascSplitRestOK` from its cases left (`UpCascSplitRest2OK`): the made stop node
below the root split in time in place is proved (`writerWP_upCasc_below_madeTime`, the
heights by `writerWP_upCasc_below_ht`). -/
theorem upCascSplitRestOK_of_rest2 (c : Ctx) (base : View BVal) (KO : KindOracle) (B : NodeId)
    (H : NodeId → Nat → Prop) (h : UpCascSplitRest2OK c base KO B H) : UpCascSplitRestOK c base KO B H := by
  intro w w3 top0 pre cv rk X Nn K depth stop w2 S g compact s hvc hm hsa2 hp hvB hk hICEk hvo hkw hpos hB hbook
    hI hRO hICE hLC hJ2 hMF3 hr03 hJ3 hH3 hwf3 hlen3 hX0 hkey hrk hvis hpX hpK hlkX hXN hlinkK hne hall hleaf
    hkids hdepth hsD hbetween hstp hLE hJw2 hgeq hsl hDR hcase hlook hnsp
  by_cases hmt : 0 < stop ∧ (Nn stop).firstTime = some c.i ∧ (!compact && decide ((S.lastVersionGivenDel c.i
      (bitsUnion S.lastBitmap (S.bitsOf (K (stop + 1))))).size > c.p.splitAbove)) = false
  · obtain ⟨hs0, hmade, htime⟩ := hmt
    obtain ⟨D, rfl⟩ : ∃ D, stop = D + 1 := ⟨stop - 1, by omega⟩
    have hJv := kdJP_note c base B top0 hB KO B hvB hk _ "up.stop-at-segment-leaf" w2 hJw2
    have hcu : CacheUnique ({ w2 with trail := "up.stop-at-segment-leaf" :: w2.trail } : W) :=
      cacheUnique_of_book hJv.1.1.book
    obtain ⟨hlinks2, hwf2⟩ := linksWf_of_book c base B top0 _ w2 hB hJv.1.1 (Or.inr ⟨_, rfl⟩)
    have hHt := writerWP_upCasc_below_ht c base hsa2 B hpos w w3 X Nn K depth D w2 _ S hI hRO hr03 hpX hpK hlkX
      hXN hlinkK hsD hX0 hLE (Or.inr ⟨_, rfl⟩) hsl hcu hlinks2 hwf2 hvo hJ3.2.1 hH3 hwf3
      (takeJ2_of_readsAs c base B w w3 hJ2 hr03) hJv.1.2.1 hgeq hJv.2 compact s
    have hL := writerWP_upCasc_below_madeTime c base hvc hsa2 KO B hvB hk hB w w3 top0 pre cv rk X Nn K depth D w2
      S g hI hr03 hLC hlen3 hX0 hkey hrk hvis hpX hpK hlkX hXN hlinkK hleaf hsD hstp hLE hJw2 hsl hmade hlook
      compact s htime
    exact writerWP_mono (writerWP_and hHt hL) (fun _ _ h => h)
  · exact h w w3 top0 pre cv rk X Nn K depth stop w2 S g compact s hvc hm hsa2 hp hvB hk hICEk hvo hkw hpos hB
      hbook hI hRO hICE hLC hJ2 hMF3 hr03 hJ3 hH3 hwf3 hlen3 hX0 hkey hrk hvis hpX hpK hlkX hXN hlinkK hne hall
      hleaf hkids hdepth hsD hbetween hstp hLE hJw2 hgeq hsl hDR hcase hlook hnsp hmt

/-- `UpCascSplitRest2OK` at the contexts of the runs of R. -/
def UpCascSplitRest2Runs (p : Params) (R : Struct BVal → Time → Prop) : Prop :=
  ∀ ts (tx : Tx), Within p (ts ++ [tx]) → R (treeRun p ts) ts.length →
    UpCascSplitRest2OK (ctxOf p ts) (viewOf (treeRun p ts)) (kindOracleOf p (treeRun p ts)) tx.base
      (htOracleOf p (treeRun p ts))

/-- `UpCascCallRuns` (the premise of `delCaseLive_emptyCasc`) from the full stop node's
cases left at the runs (`UpCascSplitRest2Runs`). -/
theorem upCascCallRuns_of_rest2 (p : Params) (R : Struct BVal → Time → Prop) (h : UpCascSplitRest2Runs p R) :
    UpCascCallRuns p R :=
  upCascCallRuns_of_rest p R (fun ts tx hw hr => upCascSplitRestOK_of_rest2 _ _ _ _ _ (h ts tx hw hr))

/-- The full stop node's cases left after the made stop node's splits below the root
(bergdb 030-01, step 6): a stop node below the root not made by the transaction split
in time (the copy the hole, below a parent with room or with the cascade), and a made
space root. -/
def UpCascSplitRest3OK (c : Ctx) (base : View BVal) (KO : KindOracle) (B : NodeId)
    (H : NodeId → Nat → Prop) : Prop :=
  ∀ (w w3 : W) (top0 : Top) (pre : List Nat) (cv : Nat) (rk : NodeId)
    (X : Nat → NodeId) (Nn : Nat → KNode) (K : Nat → Nat) (depth stop : Nat) (w2 : W) (S : KNode)
    (g : Nat) (compact : Bool) (s : String),
    ViewCoherent c base → c.p.merges = true → 2 ≤ c.p.splitAbove → MergeParamsOK c.p →
    ViewIdsBelow B c.view → ViewKinds KO B c → ICEFromKinds c base KO B →
    ViewHtOK H B c → ViewKlongsWf c.p c.view → 0 < c.i →
    PutBase c base B → PutBook c B top0 w → PutInv c base w →
    RangeOrder (wNode c.p base w) c.i w.top.rootKey →
    InnerChildrenExist (wNode c.p base w) c.i w.top.rootKey →
    LiveCounts c.p (wNode c.p base w) c.i w.top.rootKey →
    TakeJ2 c base B w → (∀ x o, w3.madeFor.lookup x = some o → o < B) →
    ReadsAs c.p base w w3 → KdJ c B top0 KO B w3 → HtInv H B c w3 → WriterKlongsWf w3 →
    w3.path.length = depth + 1 → X 0 = w.top.rootKey →
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
    (Nn depth).leaf = true →
    (∀ c' z, (c', z) ∈ (Nn depth).liveAt c.i → wNode c.p base w z = none) →
    0 < depth → stop < depth →
    (∀ i, stop < i → i < depth →
      (Nn i).allKeysIn (bitsUnion (Nn i).lastBitmap ((Nn i).bitsOf (K (i + 1)))) = true) →
    ((Nn stop).allKeysIn (bitsUnion (Nn stop).lastBitmap ((Nn stop).bitsOf (K (stop + 1)))) = true →
      stop = 0 ∧ (Nn 0).leaf = true) →
    UpLoopEnd c B X Nn depth stop w3 w2 S → KdJP c B top0 KO B w3.path w2 → w2.gh = w3.gh →
    (Nn stop).leaf = true → ¬ DelRoom c (K (stop + 1)) S →
    (0 < stop ∨ (Nn 0).firstTime = some c.i) →
    w2.gh.lookup (X stop) = some (g, 0) →
    ¬ (0 < stop ∧ (Nn stop).firstTime ≠ some c.i ∧ compact = false ∧
      c.p.splitAbove < (S.lastVersionGivenDel c.i (bitsUnion S.lastBitmap (S.bitsOf (K (stop + 1))))).size) →
    ¬ (0 < stop ∧ (Nn stop).firstTime = some c.i ∧ (!compact && decide ((S.lastVersionGivenDel c.i
      (bitsUnion S.lastBitmap (S.bitsOf (K (stop + 1))))).size > c.p.splitAbove)) = false) →
    ¬ (0 < stop ∧ (Nn stop).firstTime = some c.i ∧ compact = false ∧
      c.p.splitAbove < (S.lastVersionGivenDel c.i (bitsUnion S.lastBitmap (S.bitsOf (K (stop + 1))))).size) →
    WriterWP (handleFull stop (X stop)
        (S.lastVersionGivenDel c.i (bitsUnion S.lastBitmap (S.bitsOf (K (stop + 1))))) compact) c
      ({ ({ w2 with trail := "up.stop-at-segment-leaf" :: w2.trail } : W) with
        trail := s :: ({ w2 with trail := "up.stop-at-segment-leaf" :: w2.trail } : W).trail } : W)
      (fun _ w' => HtInv H B c w' ∧ LiveHoleW (pre ++ [cv]) g 0 c base w')

set_option maxHeartbeats 3200000 in
/-- `UpCascSplitRest2OK` from its cases left (`UpCascSplitRest3OK`): the made stop node
below the root split in space in place is proved (`writerWP_upCasc_below_madeSpaceH`). -/
theorem upCascSplitRest2OK_of_rest3 (c : Ctx) (base : View BVal) (KO : KindOracle) (B : NodeId)
    (H : NodeId → Nat → Prop) (h : UpCascSplitRest3OK c base KO B H) : UpCascSplitRest2OK c base KO B H := by
  intro w w3 top0 pre cv rk X Nn K depth stop w2 S g compact s hvc hm hsa2 hp hvB hk hICEk hvo hkw hpos hB hbook
    hI hRO hICE hLC hJ2 hMF3 hr03 hJ3 hH3 hwf3 hlen3 hX0 hkey hrk hvis hpX hpK hlkX hXN hlinkK hne hall hleaf
    hkids hdepth hsD hbetween hstp hLE hJw2 hgeq hsl hDR hcase hlook hnsp hmt
  by_cases hms : 0 < stop ∧ (Nn stop).firstTime = some c.i ∧ compact = false ∧
      c.p.splitAbove < (S.lastVersionGivenDel c.i (bitsUnion S.lastBitmap (S.bitsOf (K (stop + 1))))).size
  · obtain ⟨hs0, hmade, hc, hsz⟩ := hms
    obtain ⟨D, rfl⟩ : ∃ D, stop = D + 1 := ⟨stop - 1, by omega⟩
    have hJv := kdJP_note c base B top0 hB KO B hvB hk _ "up.stop-at-segment-leaf" w2 hJw2
    have hcu : CacheUnique ({ w2 with trail := "up.stop-at-segment-leaf" :: w2.trail } : W) :=
      cacheUnique_of_book hJv.1.1.book
    obtain ⟨hlinks2, hwf2⟩ := linksWf_of_book c base B top0 _ w2 hB hJv.1.1 (Or.inr ⟨_, rfl⟩)
    refine writerWP_mono (writerWP_upCasc_below_madeSpaceH c base hsa2 hp B hpos w w3 X Nn K depth D w2 _ S hI
      hRO hr03 hLC hpX hpK hlkX hXN hlinkK hsD hX0 hLE (Or.inr ⟨_, rfl⟩) hsl hmade hcu hlinks2 hwf2 hvo hJ3.2.1
      hH3 hwf3 (takeJ2_of_readsAs c base B w w3 hJ2 hr03) hJv.1.2.1 hgeq hJv.2 compact hc s hsz) ?_
    rintro _ w' ⟨hHt, hE⟩
    exact ⟨hHt, liveEdgesH_of_liveEdges _ _ _ _ _ hE⟩
  · exact h w w3 top0 pre cv rk X Nn K depth stop w2 S g compact s hvc hm hsa2 hp hvB hk hICEk hvo hkw hpos hB
      hbook hI hRO hICE hLC hJ2 hMF3 hr03 hJ3 hH3 hwf3 hlen3 hX0 hkey hrk hvis hpX hpK hlkX hXN hlinkK hne hall
      hleaf hkids hdepth hsD hbetween hstp hLE hJw2 hgeq hsl hDR hcase hlook hnsp hmt hms

/-- `UpCascSplitRest3OK` at the contexts of the runs of R. -/
def UpCascSplitRest3Runs (p : Params) (R : Struct BVal → Time → Prop) : Prop :=
  ∀ ts (tx : Tx), Within p (ts ++ [tx]) → R (treeRun p ts) ts.length →
    UpCascSplitRest3OK (ctxOf p ts) (viewOf (treeRun p ts)) (kindOracleOf p (treeRun p ts)) tx.base
      (htOracleOf p (treeRun p ts))

/-- `UpCascCallRuns` (the premise of `delCaseLive_emptyCasc`) from the full stop node's
cases left at the runs (`UpCascSplitRest3Runs`). -/
theorem upCascCallRuns_of_rest3 (p : Params) (R : Struct BVal → Time → Prop) (h : UpCascSplitRest3Runs p R) :
    UpCascCallRuns p R :=
  upCascCallRuns_of_rest2 p R (fun ts tx hw hr => upCascSplitRest2OK_of_rest3 _ _ _ _ _ (h ts tx hw hr))

end SIS.Tree
