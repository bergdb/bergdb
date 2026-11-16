/-
`htb`'s sites (bergdb 025-05, step 8): the delete's checked copy with any `afterDelete`
(`putKvDelChk2G`), and the copy that checks, at each call of `afterDelete`, the state
the stratum gives there and, after the merges' loop, the take-back's node facts
(`afterDeleteH`). The delete runs as it at the induction's runs (`opDelChkH_holds`):
as `putKvDelChk6` (the stratum), then as the copy with the checked merges and collapse
(`rwp_afterDeleteJH`), then on the checked upward delete (`rwp_putKvDelChk5G`, the proof of
`rwp_putKvDelChk5` for any `afterDelete`).
-/
import SIS.Tree.DeadTop

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! ## The checked copy with any `afterDelete` -/


/-- `deleteUpwardChk2` with any calls of the merges and root collapse. -/
def deleteUpwardChk2G (ad : Key → Nat → Nat → M Unit) (leaf : NodeId) (depth : Nat) (cv : Nat) (key : Key) : M Bool := do
  let c ← read
  let tt := c.i
  let n ← getNode leaf
  let leafDel := n.lastBitmap
  let leafUnion := bitsUnion leafDel (n.bitsOf cv)
  if leafUnion == leafDel then return true
  if !n.allKeysIn leafUnion then
    let (g, h) ← ghOf leaf
    let _ ← appendDeleteKlong leaf depth cv
    ad key g h
    return false
  let stop ← climb depth
  if stop == depth then
    note "up.root-kept-empty"
    let _ ← appendDeleteKlong leaf depth cv
    return false
  note "up.climb"
  let path := (← (MonadState.get : M W)).path
  let _segment ← (path.take stop).foldlM (fun s (e : Option Nat × NodeId) => do
    pure (if (← getNode e.2).leaf then s + 1 else s)) 0
  for j in List.range (depth - stop) do
    let k := depth - j
    let x ← pathNode k
    let xn ← getNode x
    if xn.firstTime == some tt then takeBackChk x (← pathNode (k - 1)) (← klongAt k)
    else
      note "up.unlink"
      unlink x
  let s ← pathNode stop
  let cs ← klongAt (stop + 1)
  let sn ← getNode s
  let (gs, hs) ← ghOf s
  if !sn.leaf then throw "check: the upward delete's stop node is no segment leaf"
  note "up.stop-at-segment-leaf"
  let _ ← appendDeleteKlong s stop cs
  ad key gs hs
  return false

/-- `setValueDelChk2` with `deleteUpwardChk2G ad`. -/
def setValueDelChk2G (ad : Key → Nat → Nat → M Unit) (segRoot : NodeId) (cv : Nat) (key : Key) : M Bool := do
  let c ← read
  let leaf ← descendLte cv c.p.fuel segRoot
  let noop ← deleteUpwardChk2G ad leaf ((← pathSize) - 1) cv key
  if !noop then
    let _ ← fresh
  pure noop

/-- `putSegsDelChk2` with `setValueDelChk2G ad`. -/
def putSegsDelChk2G (ad : Key → Nat → Nat → M Unit) (key : Key) : List Nat → NodeId → M Bool
  | [], _ => throw "corrupt: a key without segments"
  | [cv], segRoot => setValueDelChk2G ad segRoot cv key
  | cv :: rest, segRoot => do
    match ← setNode segRoot cv false with
    | none => pure true
    | some next => putSegsDelChk2G ad key rest next

/-- `putKvDelChk2` with `putSegsDelChk2G ad`. -/
def putKvDelChk2G (ad : Key → Nat → Nat → M Unit) (key : Key) : M Bool := do
  pathClear
  let root ← findRoot
  putSegsDelChk2G ad key key root


theorem deleteUpwardChk2_eqG (leaf : NodeId) (depth cv : Nat) (key : Key) :
    deleteUpwardChk2 leaf depth cv key = deleteUpwardChk2G afterDeleteChk leaf depth cv key := rfl

theorem setValueDelChk2_eqG (segRoot : NodeId) (cv : Nat) (key : Key) :
    setValueDelChk2 segRoot cv key = setValueDelChk2G afterDeleteChk segRoot cv key := rfl

theorem putSegsDelChk2_eqG (key : Key) :
    ∀ (segs : List Nat) (r : NodeId), putSegsDelChk2 key segs r = putSegsDelChk2G afterDeleteChk key segs r := by
  intro segs
  induction segs with
  | nil => intro r; rfl
  | cons cv rest ih =>
    intro r
    cases rest with
    | nil => rfl
    | cons d rest' =>
      unfold putSegsDelChk2 putSegsDelChk2G
      simp only [ih]
      rfl

theorem putKvDelChk2_eqG (key : Key) : putKvDelChk2 key = putKvDelChk2G afterDeleteChk key := by
  unfold putKvDelChk2 putKvDelChk2G
  simp only [putSegsDelChk2_eqG]

/-! ## The two runs: the checked upward delete with any `afterDelete` -/

set_option maxHeartbeats 3200000 in
/-- The upward delete without the loop's `checkFree` runs as `deleteUpwardChk2`
when the fill, `PutInv` and the take-back's node facts hold at the delete's
start: the loop's invariant `HoldInv` gives each take-back's check
(`step_takeBack`, `step_unlink`). -/
theorem rwp_deleteUpwardChk5G (ad : Key → Nat → Nat → M Unit) (c : Ctx) (base : View BVal) (w0 : W) (B : NodeId)
    (hvg : ViewGood B c) (hI0 : PutInv c base w0) (hJ2 : TakeJ2 c base B w0)
    (hLC : LiveCounts c.p (wNode c.p base w0) c.i w0.top.rootKey) (hm : c.p.merges = true)
    (X : Nat → NodeId) (Nn : Nat → KNode) (K : Nat → Nat) (depth : Nat)
    (hX0 : X 0 = w0.top.rootKey)
    (hXN : ∀ i, i ≤ depth → wNode c.p base w0 (X i) = some (Nn i))
    (hlinkK : ∀ i, 0 < i → i ≤ depth → (K i, X i) ∈ (Nn (i - 1)).liveAt c.i)
    (w3 : W) (hr03 : ReadsAs c.p base w0 w3) (hcg3 : CacheGood B c w3)
    (hnd3 : (w3.nodes.map Prod.fst).Nodup)
    (hpX : ∀ i, i ≤ depth → (w3.path[i]?).map (·.2) = some (X i))
    (hpK : ∀ i, 0 < i → i ≤ depth → w3.path[i]? = some (some (K i), X i))
    (hlkX : ∀ i, i ≤ depth → w3.nodes.lookup (X i) = some (Nn i))
    (hmf : ∀ x o, w3.madeFor.lookup x = some o → (c.view o).isSome = true)
    (cv : Nat) (key : Key) :
    RWP (deleteUpwardP ad (X depth) depth cv key) (deleteUpwardChk2G ad (X depth) depth cv key) c w3 := by
  have htimes := hI0.times
  have hdist := chain_dist c base w0 hI0 X Nn K depth hX0 hXN hlinkK
  unfold deleteUpwardP deleteUpwardChk2G
  refine rwp_read ?_
  refine rwp_getNode_known (X depth) (Nn depth) (hlkX depth (Nat.le_refl _)) ?_
  dsimp only
  by_cases h1 : (bitsUnion (Nn depth).lastBitmap ((Nn depth).bitsOf cv) == (Nn depth).lastBitmap) = true
  · simp only [h1, ↓reduceIte]; exact rwp_refl _ _ _
  simp only [h1, Bool.false_eq_true, ↓reduceIte]
  by_cases h2 : (!(Nn depth).allKeysIn (bitsUnion (Nn depth).lastBitmap ((Nn depth).bitsOf cv))) = true
  · simp only [h2, ↓reduceIte]; exact rwp_refl _ _ _
  simp only [h2, Bool.false_eq_true, ↓reduceIte]
  have hall : (Nn depth).allKeysIn (bitsUnion (Nn depth).lastBitmap ((Nn depth).bitsOf cv)) = true := by
    simpa using h2
  refine rwp_bind _ (writerWP_climb c X Nn K depth w3 hpX hpK hlkX) ?_
  rintro stop v ⟨hv, hsle, hbetween, -, -, -⟩
  subst v
  by_cases h3 : (stop == depth) = true
  · simp only [h3, ↓reduceIte]; exact rwp_refl _ _ _
  simp only [h3, Bool.false_eq_true, ↓reduceIte]
  have hsD : stop < depth := by
    have : stop ≠ depth := fun he => h3 (by simp [he])
    omega
  -- the fill: below the stop node, every node of the path is the parent of an emptied node
  have hleafAt : ∀ k, stop < k → k ≤ depth → (Nn (k - 1)).leaf = true := by
    intro k hk1 hk2
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    cases hl : (Nn j).leaf with
    | true => rfl
    | false =>
      exfalso
      rcases Nat.lt_or_ge (j + 1) depth with hlt | hge
      · exact stopLeaf_of_liveCounts c.p (wNode c.p base w0) c.i w0.top.rootKey hLC hm X Nn K depth hX0
          hXN hlinkK j hk2 hl (K (j + 1 + 1)) (htimes _ _ (hXN (j + 1) hk2))
          (hbetween (j + 1) hk1 hlt)
      · have he : j + 1 = depth := by omega
        subst he
        exact stopLeaf_of_liveCounts c.p (wNode c.p base w0) c.i w0.top.rootKey hLC hm X Nn K (j + 1) hX0
          hXN hlinkK j (Nat.le_refl _) hl cv (htimes _ _ (hXN (j + 1) (Nat.le_refl _))) hall
  -- note, the path, the segment's fold: the state kept but the trail
  refine rwp_bind (fun _ v => v = { w3 with trail := "up.climb" :: w3.trail })
    (by simp only [note, writerWP_modify]) ?_
  rintro _ v1 hv1
  subst hv1
  refine rwp_bind (fun a v => a = { w3 with trail := "up.climb" :: w3.trail } ∧
      v = { w3 with trail := "up.climb" :: w3.trail })
    ((writerWP_get c _ _).mpr ⟨rfl, rfl⟩) ?_
  rintro a v2 ⟨ha, hv2⟩
  subst ha; subst hv2
  refine rwp_bind (fun _ v => v = { w3 with trail := "up.climb" :: w3.trail })
    (writerWP_foldlM_same c _ _ _ ?_ 0) ?_
  · intro b e he
    simp only [writerWP_bind]
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp he
    rw [List.getElem?_take] at hi
    split at hi
    · rename_i hil
      have hx := hpX i (by omega)
      have hi' : w3.path[i]? = some e := hi
      rw [hi'] at hx
      simp only [Option.map_some, Option.some.injEq] at hx
      rw [writerWP_getNode_known e.2 (Nn i) c _ (by rw [hx]; exact hlkX i (by omega))]
      simp only [writerWP_pure]
    · cases hi
  intro seg v3 hv3
  subst hv3
  rw [List.range_eq_range']
  refine rwp_forIn_range'_bind c _ _ _ _ (fun j v => HoldInv c w3 B X Nn depth (depth - j) v)
    (depth - stop) 0 ?_ _ ?_ ?_
  · -- a step of the loop
    intro j _ hj v hH
    have hk1 : stop < depth - j := by omega
    have hk2 : depth - j ≤ depth := by omega
    have hk0 : 0 < depth - j := by omega
    have hpar : (Nn (depth - j - 1)).leaf = true := hleafAt (depth - j) hk1 hk2
    obtain ⟨n', hn', -⟩ := hH.2.2.2.2.2.2.2
    have hpx : (v.path[depth - j]?).map (·.2) = some (X (depth - j)) := by rw [hH.1.1.1]; exact hpX _ hk2
    have hpx1 : (v.path[depth - j - 1]?).map (·.2) = some (X (depth - j - 1)) := by
      rw [hH.1.1.1]; exact hpX _ (by omega)
    have hpk : v.path[depth - j]? = some (some (K (depth - j)), X (depth - j)) := by
      rw [hH.1.1.1]; exact hpK _ (by omega) hk2
    have hidx : depth - (j + 1) = depth - j - 1 := by omega
    refine ⟨?_, ?_⟩
    · refine rwp_bind (fun x v' => x = X (depth - j) ∧ v' = v)
        (writerWP_pathNode_known _ _ c v hpx _ ⟨rfl, rfl⟩) ?_
      rintro x v' ⟨hx, hv'⟩
      subst hx; subst v'
      refine rwp_getNode_known _ n' hn' ?_
      by_cases hf : (n'.firstTime == some c.i) = true
      · simp only [hf, ↓reduceIte]
        refine rwp_bind (fun y v' => y = X (depth - j - 1) ∧ v' = v)
          (writerWP_pathNode_known _ _ c v hpx1 _ ⟨rfl, rfl⟩) ?_
        rintro y v' ⟨hy, hv'⟩
        subst hy; subst v'
        refine rwp_bind (fun y v' => y = K (depth - j) ∧ v' = v)
          (writerWP_klongAt_known _ _ _ c v hpk _ ⟨rfl, rfl⟩) ?_
        rintro y v' ⟨hy, hv'⟩
        subst hy; subst v'
        have hst := step_takeBack c base w0 w3 B hvg hI0 hJ2 hr03 X Nn K depth (depth - j) hk0 hk2 hX0 hXN
          hlinkK hdist hlkX hpar hmf v hH n' hn' (by simpa using hf)
        exact rwp_bind2 (fun _ _ => True) hst.1 (fun _ _ _ => trivial) (fun _ _ _ => rwp_refl _ _ _)
      · simp only [hf, Bool.false_eq_true, ↓reduceIte]
        exact rwp_refl _ _ _
    · simp only [writerWP_bind]
      refine writerWP_pathNode_known _ _ c v hpx _ ?_
      refine (writerWP_getNode_known _ n' c v hn' _).mpr ?_
      split
      · rename_i hf
        simp only [writerWP_bind]
        refine writerWP_pathNode_known _ _ c v hpx1 _ ?_
        refine writerWP_klongAt_known _ _ _ c v hpk _ ?_
        have hst := step_takeBack c base w0 w3 B hvg hI0 hJ2 hr03 X Nn K depth (depth - j) hk0 hk2 hX0 hXN
          hlinkK hdist hlkX hpar hmf v hH n' hn' (by simpa using hf)
        refine writerWP_mono hst.2 ?_
        intro _ u hu
        simp only [writerWP_pure]
        refine ⟨by first | trivial | rfl, ?_⟩
        rw [hidx]; exact hu
      · have hsu := step_unlink c base w0 w3 B hvg hI0 X Nn depth (depth - j) hk0 hk2 hXN hdist hlkX v hH
        simp only [writerWP_bind] at hsu ⊢
        refine writerWP_mono hsu ?_
        intro _ u hu
        refine writerWP_mono hu ?_
        intro _ u' hu'
        simp only [writerWP_pure]
        refine ⟨by first | trivial | rfl, ?_⟩
        rw [hidx]; exact hu'
  · -- the loop's start
    show HoldInv c w3 B X Nn depth (depth - 0) _
    rw [Nat.sub_zero]
    refine ⟨⟨⟨rfl, fun y n hy => ⟨n, hy, rfl⟩⟩, rfl⟩, hcg3, hnd3, rfl, fun y hy => hy, fun y _ => rfl,
      fun j h1 h2 => absurd h2 (by omega), Nn depth, hlkX depth (Nat.le_refl _), Or.inl rfl⟩
  · -- the stop node
    intro v4 hH4
    have hv4 : LeafFrM w3 v4 := hH4.1
    have hps : (v4.path[stop]?).map (·.2) = some (X stop) := by rw [hv4.1.1]; exact hpX _ (by omega)
    have hpk : v4.path[stop + 1]? = some (some (K (stop + 1)), X (stop + 1)) := by
      rw [hv4.1.1]; exact hpK _ (by omega) (by omega)
    obtain ⟨sn, hsn, hsl⟩ := hv4.1.2 _ _ (hlkX stop (by omega))
    have hsleaf : sn.leaf = true := by
      rw [hsl]; have := hleafAt (stop + 1) (by omega) (by omega); simpa using this
    refine rwp_bind (fun x v' => x = X stop ∧ v' = v4)
      (writerWP_pathNode_known _ _ c v4 hps _ ⟨rfl, rfl⟩) ?_
    rintro x v' ⟨hx, hv'⟩
    subst hx; subst v'
    refine rwp_bind (fun y v' => y = K (stop + 1) ∧ v' = v4)
      (writerWP_klongAt_known _ _ _ c v4 hpk _ ⟨rfl, rfl⟩) ?_
    rintro y v' ⟨hy, hv'⟩
    subst hy; subst v'
    refine rwp_getNode_known _ sn hsn ?_
    refine rwp_bind_any (fun gh v5 => ?_)
    simp only [hsleaf, ↓reduceIte, Bool.not_true, Bool.false_eq_true]
    exact rwp_refl _ _ _


set_option maxHeartbeats 1600000 in
/-- The last segment's descent and the upward delete, for the two copies: the
path from w0's root as the upward delete's refinement asks, the cache's books kept. -/
theorem rwp_setValueDelChk5G (ad : Key → Nat → Nat → M Unit) (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base) (w0 : W) (B : NodeId)
    (hvg : ViewGood B c) (hI0 : PutInv c base w0) (hJ2 : TakeJ2 c base B w0)
    (hLC : LiveCounts c.p (wNode c.p base w0) c.i w0.top.rootKey) (hm : c.p.merges = true)
    (hmf0 : ∀ x o, w0.madeFor.lookup x = some o → (c.view o).isSome = true)
    (r : NodeId) (cv : Nat) (key : Key) (w : W) (hS : SegInv c base w0 w r) (hmw : w.madeFor = w0.madeFor)
    (hcg : CacheGood B c w) (hu : UniqueCache B w)
    (ht : ∀ q ∈ eqVisits (wNode c.p base w0) c.i cv c.p.fuel r, w0.taken.contains q.1 = false) :
    RWP (setValueDP ad r cv key) (setValueDelChk2G ad r cv key) c w := by
  obtain ⟨hr0, hpre0, ps, hp, hl, he, hc⟩ := hS
  have ht1 : ∀ q ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel r, w.taken.contains q.1 = false := by
    rw [hr0.1, hr0.2.2.1]; exact ht
  unfold setValueDP setValueDelChk2G
  refine rwp_read ?_
  refine rwp_bind _ (writerWP_and (writerWP_and (writerWP_and (writerWP_and (writerWP_and
    (writerWP_descendLte_reads cv c base hvc c.p.fuel r w ht1)
    (writerWP_descendLte_steps cv c base hvc c.p.fuel r w ht1))
    (writerWP_descendLte_cache cv c base hvc c.p.fuel r w ht1))
    (writerWP_descendLte_madeFor cv c c.p.fuel r w))
    (good_descendLte B cv c.p.fuel r c w hvg hcg))
    (uniqueCache_descendLte (base := B) cv c.p.fuel r c w hvg.ids hu)) ?_
  rintro L w3 ⟨⟨⟨⟨⟨⟨hr3, n, hn, hnl, hlk3, hvisL, -⟩, ⟨steps, hpf, hp3, hLe⟩⟩, ⟨hcache3, -, hpre3⟩⟩, hm3⟩, hcg3⟩,
    hu3, -⟩
  have hr03 : ReadsAs c.p base w0 w3 := ReadsAs.trans c.p base w0 w w3 hr0 hr3
  rw [hr0.1] at hn hvisL hpf hcache3
  refine rwp_bind _ (kd_pathSize c w3) ?_
  rintro sz v ⟨hv, hsz⟩
  subst hsz; subst v
  refine rwp_bind2 (fun _ _ => True) ?_ (fun _ _ _ => trivial) (fun _ _ _ => rwp_refl _ _ _)
  -- the path from w0's root
  obtain ⟨P, hP⟩ : ∃ P, P = ps ++ steps := ⟨_, rfl⟩
  have hp3' : w3.path = (none, w0.top.rootKey) :: P := by rw [hp3, hp, hP]; simp
  have hlinkP : LinkedFrom (wNode c.p base w0) c.i w0.top.rootKey P := by
    rw [hP]
    exact LinkedFrom.append _ _ _ ps steps hl (by rw [he]; exact LinkedFrom.of_pathFrom _ _ cv r steps hpf)
  have hXD : nodeAt w0.top.rootKey P P.length = L := by
    rw [nodeAt_last, hP, pathEnd_append_gen, he, hLe]
  have hvis := PathFrom.mem_eqVisits _ _ _ c.p.fuel r steps hpf
    (fun mm hmm => by rw [← hLe, hn] at hmm; cases hmm; exact hnl) (by rw [← hLe]; exact hvisL)
  have hgetP := LinkedFrom.get _ _ _ P hlinkP
  have hXN : ∀ i, i ≤ P.length → wNode c.p base w0 (nodeAt w0.top.rootKey P i) =
      some ((wNode c.p base w0 (nodeAt w0.top.rootKey P i)).getD n) := by
    intro i hi
    rcases Nat.lt_or_ge i P.length with hlt | hge
    · obtain ⟨_, n', _, h2, _⟩ := hgetP i hlt
      rw [h2]; rfl
    · have : i = P.length := by omega
      subst this
      rw [hXD, hn]; rfl
  have hlkX : ∀ i, i ≤ P.length → w3.nodes.lookup (nodeAt w0.top.rootKey P i) =
      some ((wNode c.p base w0 (nodeAt w0.top.rootKey P i)).getD n) := by
    intro i hi
    have hw := hXN i hi
    rcases Nat.lt_or_ge i ps.length with hlt | hge
    · have hmem : nodeAt w0.top.rootKey P i ∈ (w0.top.rootKey :: ps.map (·.2)).dropLast := by
        rw [hP, nodeAt_append_left _ _ _ _ (by omega)]
        exact nodeAt_mem_dropLast _ _ _ hlt
      exact lookup_of_isPrefix _ _ hpre3 _ _ (hc _ hmem _ hw)
    · obtain ⟨j, hj⟩ : ∃ j, i = ps.length + j := ⟨i - ps.length, by omega⟩
      have hXj : nodeAt w0.top.rootKey P i = nodeAt r steps j := by
        rw [hP, hj, nodeAt_append_right, he]
      have hvj : (nodeAt r steps j, cv) ∈ eqVisits (wNode c.p base w0) c.i cv c.p.fuel r := by
        rcases Nat.eq_zero_or_pos j with h0 | h0
        · rw [h0, nodeAt_zero]; exact hvis.1
        · have hjl : j ≤ steps.length := by
            have : P.length = ps.length + steps.length := by rw [hP]; simp
            omega
          obtain ⟨e, he1, he2⟩ := nodeAt_mem_steps r steps j h0 hjl
          rw [← he2]; exact hvis.2 e he1
      rw [hXj] at hw ⊢
      exact hcache3 _ _ hvj hw
  have hKP : ∀ i, 0 < i → i ≤ P.length →
      P[i - 1]? = some (some (((P[i - 1]?).bind (·.1)).getD 0), nodeAt w0.top.rootKey P i) ∧
      (((P[i - 1]?).bind (·.1)).getD 0, nodeAt w0.top.rootKey P i) ∈
        ((wNode c.p base w0 (nodeAt w0.top.rootKey P (i - 1))).getD n).liveAt c.i := by
    intro i h1 h2
    obtain ⟨k, n', e1, e2, e3⟩ := hgetP (i - 1) (by omega)
    have hi : i - 1 + 1 = i := by omega
    rw [hi] at e1 e3
    rw [e1, e2]
    exact ⟨rfl, e3⟩
  have hpX : ∀ i, i ≤ P.length → (w3.path[i]?).map (·.2) = some (nodeAt w0.top.rootKey P i) := by
    intro i hi
    have hl' : i < (w0.top.rootKey :: P.map (·.2)).length := by simp; omega
    rw [hp3', ← List.getElem?_map, List.map_cons, List.getElem?_eq_getElem hl']
    simp [nodeAt, List.getElem?_eq_getElem hl']
  have hpK : ∀ i, 0 < i → i ≤ P.length →
      w3.path[i]? = some (some (((P[i - 1]?).bind (·.1)).getD 0), nodeAt w0.top.rootKey P i) := by
    intro i h1 h2
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    rw [hp3', List.getElem?_cons_succ]
    exact (hKP (j + 1) h1 h2).1
  have hlen : w3.path.length - 1 = P.length := by rw [hp3']; simp
  rw [hlen, ← hXD]
  exact rwp_deleteUpwardChk5G ad c base w0 B hvg hI0 hJ2 hLC hm (fun i => nodeAt w0.top.rootKey P i)
    (fun i => (wNode c.p base w0 (nodeAt w0.top.rootKey P i)).getD n)
    (fun i => ((P[i - 1]?).bind (·.1)).getD 0) P.length (by simp [nodeAt]) hXN
    (fun i h1 h2 => (hKP i h1 h2).2) w3 hr03 hcg3 hu3.2 hpX hpK hlkX
    (fun x o ho => hmf0 x o (by rw [← hmw, ← hm3]; exact ho)) cv key

/-- The delete's segments, for the two copies. -/
theorem rwp_putSegsDelChk5G (ad : Key → Nat → Nat → M Unit) (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base) (w0 : W) (B : NodeId)
    (hvg : ViewGood B c) (hI0 : PutInv c base w0) (hJ2 : TakeJ2 c base B w0)
    (hLC : LiveCounts c.p (wNode c.p base w0) c.i w0.top.rootKey) (hm : c.p.merges = true)
    (hmf0 : ∀ x o, w0.madeFor.lookup x = some o → (c.view o).isSome = true) (key : Key) :
    ∀ (segs : List Nat) (r : NodeId) (w : W), SegInv c base w0 w r → w.madeFor = w0.madeFor →
      CacheGood B c w → UniqueCache B w →
      (∀ q ∈ fromVisits (wNode c.p base w0) c.i c.p.fuel segs r, w0.taken.contains q.1 = false) →
      RWP (putSegsDP ad key segs r) (putSegsDelChk2G ad key segs r) c w := by
  intro segs
  induction segs with
  | nil => intro r w _ _ _ _ _; unfold putSegsDP putSegsDelChk2G; exact rwp_refl _ _ _
  | cons cv rest ih =>
    intro r w hS hmw hcg hu ht
    cases rest with
    | nil =>
      unfold putSegsDP putSegsDelChk2G
      exact rwp_setValueDelChk5G ad c base hvc w0 B hvg hI0 hJ2 hLC hm hmf0 r cv key w hS hmw hcg hu
        (fun q hq => ht q (by simpa [fromVisits] using hq))
    | cons d rest' =>
      unfold putSegsDP putSegsDelChk2G
      have ht0 : ∀ q ∈ eqVisits (wNode c.p base w0) c.i cv c.p.fuel r, w0.taken.contains q.1 = false :=
        fun q hq => ht q (by simp only [fromVisits]; exact List.mem_append_left _ hq)
      refine rwp_bind _ (writerWP_and (writerWP_and (writerWP_and
        (writerWP_setNode_seg c base hvc w0 cv r w hS ht0 hI0.wf)
        (writerWP_setNode_madeFor r cv c w)) (good_setNode B r cv false c w hvg hcg))
        (uniqueCache_setNode (base := B) r cv false c w hvg.ids hu)) ?_
      rintro res v ⟨⟨⟨hres, hmv⟩, hcgv⟩, huv, -⟩
      cases res with
      | none => exact rwp_refl _ _ _
      | some y =>
        obtain ⟨hS', hg⟩ := hres y rfl
        refine ih y v hS' (hmv.trans hmw) hcgv huv ?_
        intro q hq
        apply ht q
        simp only [fromVisits]
        apply List.mem_append_right
        rw [hg]
        exact hq

/-- The delete's two copies run alike from a state with `PutInv`, the fill, the
made-for ids nodes of the view, the take-back's node facts and the cache's books. -/
theorem rwp_putKvDelChk5G (ad : Key → Nat → Nat → M Unit) (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base) (w0 : W) (B : NodeId)
    (hvg : ViewGood B c) (hI : PutInv c base w0) (hJ2 : TakeJ2 c base B w0)
    (hcg : CacheGood B c w0) (hu : UniqueCache B w0)
    (hLC : LiveCounts c.p (wNode c.p base w0) c.i w0.top.rootKey) (hm : c.p.merges = true)
    (hmf0 : ∀ x o, w0.madeFor.lookup x = some o → (c.view o).isSome = true)
    (key : Key) : RWP (putKvDP ad key) (putKvDelChk2G ad key) c w0 := by
  unfold putKvDP putKvDelChk2G
  refine rwp_bind (fun _ v => v = { w0 with path := [] })
    (by unfold pathClear; simp only [writerWP_modify]) ?_
  rintro _ v1 hv1
  subst hv1
  refine rwp_bind (fun a v => a = w0.top.rootKey ∧
      v = { ({ w0 with path := [] } : W) with path := [(none, w0.top.rootKey)] })
    (by simp only [findRoot, pathAdd, writerWP_bind, writerWP_get, writerWP_modify, writerWP_pure]
        simp) ?_
  rintro a v2 ⟨ha, hv2⟩
  subst ha; subst hv2
  refine rwp_putSegsDelChk5G ad c base hvc w0 B hvg hI hJ2 hLC hm hmf0 key key _ _ ?_ rfl hcg hu (hI.pathUntaken key)
  refine ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, List.prefix_refl _, [], rfl, LinkedFrom.nil _, rfl, ?_⟩
  intro z hz
  simp at hz



/-! ## The premise without the loop's `checkFree` -/


end SIS.Tree
