/-
A full node replaced by a last version that keeps what it reached, with the
cascade above, keeps the take-back's facts (bergdb 024-12, TP7, case (4)'s full
leaf): `writerWP_handleFull_lastVF2`'s reach-back and
`writerWP_handleFull_lastShape`'s shapes, for the node at depth D + 1 below the
space root's chain from depth 0.
-/
import SIS.Tree.TakeMergeFull
import SIS.Tree.GetMergeInv

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

set_option maxHeartbeats 3200000 in
/-- `handleFull` of the node X (D + 1) with a last version `last` that keeps the
node's live children (or they are no nodes, `hkeep`) keeps `TakeJ2`, and B stays
at most the next id: on the premises of `writerWP_handleFull_lastVF2` with the
chain from the space root (s = 0), with the cascade's levels and `last` ordered
(`hord`, `hLO`) and `last` a time klong with key klongs of distinct compare
values (`hpairs`). -/
theorem writerWP_handleFull_last_j2 (fuelR : Nat) (hfR : 2 ≤ fuelR) (c : Ctx) (base : View BVal)
    (B : NodeId) (hpos : 0 < c.i) (w : W) (hJ : TakeJ2 c base B w) (hBn : B ≤ w.next)
    (hvnx : ∀ y ∈ w.vals.map (·.1), y < w.next)
    (D : Nat) (X : Nat → NodeId) (K : Nat → Nat) (Nn : Nat → KNode)
    (hX : ∀ i, 0 ≤ i → i ≤ D + 1 → (w.path[i]?).map (·.2) = some (X i))
    (hK : ∀ i, 0 < i → i ≤ D + 1 → w.path[i]? = some (some (K i), X i))
    (hlinkK : ∀ i, 0 < i → i ≤ D + 1 → (K i, X i) ∈ (Nn (i - 1)).liveAt c.i)
    (hrange : ∀ i, 0 < i → i ≤ D → ¬ ChainRoom c (Nn i) → (Nn (i - 1)).leaf = false →
      ∀ c' z, (c', z) ∈ (Nn i).live → 0 < c' →
      K i ≤ c' ∧ ∀ c'' z', (c'', z') ∈ (Nn (i - 1)).live → K i < c'' → c' < c'')
    (hlen : ∀ i, 0 ≤ i → i ≤ D → ¬ ChainRoom c (Nn i) →
      c.p.splitAbove < ((Nn i).lastVersion c.i).size →
      2 ≤ (Nn i).live.length)
    (hwf : ∀ i, 0 ≤ i → i ≤ D + 1 → klongsWf (Nn i).ks = true)
    (htimes : ∀ i, 0 ≤ i → i ≤ D + 1 → ∀ t, Klong.time t ∈ (Nn i).ks → t ≤ c.i)
    (hdist : ∀ i i', 0 ≤ i → i ≤ D + 1 → 0 ≤ i' → i' ≤ D + 1 → X i = X i' → i = i')
    (hspace : ∀ i, 0 ≤ i → i ≤ D → ¬ ChainRoom c (Nn i) →
      c.p.splitAbove < ((Nn i).lastVersion c.i).size → i = 0 ∨ (0 < i ∧ ((Nn (i - 1)).leaf = false ∨
        ((Nn i).firstTime ≠ some c.i → ∀ i', 0 < i' → i' < i → ChainOrd c K Nn i'))))
    (hord : ∀ i, 0 < i → i ≤ D → ChainOrd c K Nn i)
    (last : KNode) (compact : Bool)
    (hlwf : klongsWf last.ks = true) (hlt : ∀ s, Klong.time s ∈ last.ks → s ≤ c.i)
    (hlastV : (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode).lastVersion c.i = last)
    (hlen2 : c.p.splitAbove < last.size → 2 ≤ (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode).live.length)
    (hrangeL : c.p.splitAbove < last.size → (Nn D).leaf = false →
      ∀ c' z, (c', z) ∈ (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode).live → 0 < c' →
      K (D + 1) ≤ c' ∧ ∀ c'' z', (c'', z') ∈ (Nn D).live → K (D + 1) < c'' → c' < c'')
    (hspaceL : (!compact && decide (last.size > c.p.splitAbove)) = true →
      (Nn D).leaf = false ∨ ((Nn (D + 1)).firstTime ≠ some c.i → ∀ i', 0 < i' → i' < D + 1 → ChainOrd c K Nn i'))
    (hpairs : ∃ pairs, last.ks = newKlongs c.i pairs ∧ (pairs.map Prod.fst).Nodup)
    (hLO : LastOrd c K Nn D last)
    (hS2 : ∀ i, 0 ≤ i → i ≤ D + 1 →
      w.nodes.lookup (X i) = some (Nn i) ∧ w.taken.contains (X i) = false)
    (hS3 : TreeOK (wNode c.p base w) c.i w.top.rootKey)
    (hS4 : ∀ i, 0 ≤ i → i ≤ D + 1 → TReach (wNode c.p base w) c.i w.top.rootKey (X i))
    (hS5 : ∀ z, w.next ≤ z → w.nodes.lookup z = none ∧ w.taken.contains z = false ∧
      knodeOf c.p base z = none)
    (hS6 : ∀ u c' z, TLink (wNode c.p base w) c.i u c' z → z < w.next)
    (hR0 : w.top.rootKey = X 0)
    (hW : ∀ z zn, wNode c.p base w z = some zn → klongsWf zn.ks = true)
    (hV : TreeOK (updN (wNode c.p base w) (X (D + 1)) (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode)) c.i
      w.top.rootKey)
    (hvx : ∀ c' z, (c', z) ∈ (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode).liveAt c.i → z < w.next)
    (hkeep : ∀ cc u, (cc, u) ∈ (Nn (D + 1)).liveAt c.i →
      (∃ c', (c', u) ∈ (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode).liveAt c.i) ∨ wNode c.p base w u = none) :
    WriterWP (handleFullWith (fun q more => appendKlongs D q more) (D + 1) (X (D + 1)) [] last compact)
      c w (fun _ w' => TakeJ2 c base B w' ∧ B ≤ w'.next) := by
  have hXlt : ∀ i, 0 ≤ i → i ≤ D + 1 → X i < w.next := by
    intro i h1 h2
    obtain ⟨hl, _⟩ := hS2 i h1 h2
    rcases Nat.lt_or_ge (X i) w.next with h | h
    · exact h
    · rw [(hS5 _ h).1] at hl; cases hl
  have hN6 : ∀ i, 0 ≤ i → i ≤ D + 1 → wNode c.p base w (X i) = some (Nn i) := by
    intro i h1 h2
    obtain ⟨hl, ht⟩ := hS2 i h1 h2
    simp only [wNode, ht, Bool.false_eq_true, ↓reduceIte, hl]
  have hlevel := writerWP_handleFull_lastVF2 fuelR hfR c base w.path 0 D X K Nn (Nat.zero_le _) hX hK hlinkK
    hrange hlen hwf htimes (Or.inr rfl) hdist hspace last compact hlwf hlt hlastV hlen2 hrangeL hspaceL
    w rfl hS2 hS3 hS4 hS5 hS6 (fun _ _ => hR0) hW hV hvx
  have hshapeL := writerWP_handleFull_lastShape c w.path 0 D X K Nn (Nat.zero_le _) hX hK hlinkK hrange
    hlen hord htimes (Or.inr rfl) hdist last compact hpairs hlastV hlen2 hrangeL hLO w rfl
    (fun i h1 h2 => ⟨(hS2 i h1 h2).1, hXlt i h1 h2⟩) (fun z hz => (hS5 z hz).1)
  have hcache := @state_handleFullWith_compact (cachedFromInvariant w)
    (fun q more => appendKlongs D q more) (D + 1) (X (D + 1)) [] last compact
    (fun q more => @state_appendKlongs (cachedFromInvariant w) D q more) c w (cachedFrom_refl _ c)
  refine writerWP_mono (writerWP_and (writerWP_and hlevel hshapeL) hcache) ?_
  rintro _ w7 ⟨⟨⟨_, ⟨_, ht7, _, hn7, hv7⟩, hfr7, _, _, _, _, hRB1, hRB2⟩, hSP7⟩, hca7⟩
  have hRB1' := hRB1 hord hLO
  have hRB2' := hRB2 hord hLO
  have hN76 : ∀ z, z < w.next → (∀ i, 0 ≤ i → i ≤ D + 1 → z ≠ X i) →
      wNode c.p base w7 z = wNode c.p base w z := by
    intro z hz hnc
    simp only [wNode, ht7, hfr7 z hz hnc]
  -- the node facts
  obtain ⟨hD7, hO7, hS7, hM7, hV7⟩ := j2rest_cascade2 (wNode c.p base w) (wNode c.p base w7) c.i
    w.top.rootKey B (w.vals.map (·.1)) X Nn 0 (D + 1) w.next hpos hS3 hJ.2.1 hJ.2.2.1 hJ.2.2.2.1
    hJ.2.2.2.2.1 hJ.2.2.2.2.2 hN6 hwf htimes hS4 hvnx hN76
    (by
      intro z zn hz hz'
      have htz : w7.taken.contains z = false := by
        rw [ht7]
        rcases hz' with h | ⟨i, a, b, rfl⟩
        · exact (hS5 z h).2.1
        · exact (hS2 i a b).2
      have hlk7 : w7.nodes.lookup z = some zn := by
        unfold wNode at hz
        rw [htz] at hz
        simp only [Bool.false_eq_true, ↓reduceIte] at hz
        cases hl : w7.nodes.lookup z with
        | some m => rw [hl] at hz; exact hz
        | none =>
          exfalso
          rw [hl] at hz
          rcases hz' with h | ⟨i, a, b, rfl⟩
          · rw [(hS5 z h).2.2] at hz; cases hz
          · have := hca7 (X i) (by rw [(hS2 i a b).1]; rfl)
            rw [hl] at this; cases this
      obtain ⟨_, _, _, hsh⟩ := hSP7
      exact cascadeShapeJ2_of c (wNode c.p base w) B _ X K Nn 0 (D + 1) [] _ hJ.2.2.2.1 hJ.2.2.2.2.1 hN6
        htimes hBn (by simp) (by simp) z zn hz' (hsh z zn hlk7 hz'))
  -- (B): a node of the transaction's time is reached
  have hTt7 : TtReachedN (wNode c.p base w7) c.i w7.top.rootKey := by
    intro q qn hq hm
    by_cases hqc : ∃ i, 0 ≤ i ∧ i ≤ D + 1 ∧ q = X i
    · obtain ⟨i, a, b, rfl⟩ := hqc
      rcases hRB2'.1 i a b with h | h
      · exact h
      · exfalso
        have htz : w7.taken.contains (X i) = false := by rw [ht7]; exact (hS2 i a b).2
        simp only [wNode, htz, Bool.false_eq_true, ↓reduceIte, h, Option.some.injEq] at hq
        subst hq
        exact time_not_mem_toPrev (Nn i) c.i hpos hm
    have hnc : ∀ i, 0 ≤ i → i ≤ D + 1 → q ≠ X i := fun i a b he => hqc ⟨i, a, b, he⟩
    by_cases hqn : w.next ≤ q
    · refine hRB2'.2 q hqn ?_
      have htz : w7.taken.contains q = false := by rw [ht7]; exact (hS5 q hqn).2.1
      unfold wNode at hq
      rw [htz] at hq
      simp only [Bool.false_eq_true, ↓reduceIte] at hq
      cases hl : w7.nodes.lookup q with
      | some _ => rfl
      | none => rw [hl, (hS5 q hqn).2.2] at hq; cases hq
    rw [hN76 q (by omega) hnc] at hq
    have hTN := hJ.1 q qn hq hm
    rcases reach_updN_keep (wNode c.p base w) c.i w.top.rootKey (X (D + 1)) (Nn (D + 1))
      ⟨(Nn (D + 1)).leaf, last.ks⟩ (hN6 (D + 1) (Nat.zero_le _) (Nat.le_refl _)) hkeep q hTN with h | h
    · exact hRB1' q h hnc
    · rw [h] at hq; cases hq
  refine ⟨?_, Nat.le_trans hBn hn7⟩
  unfold TakeJ2
  rw [hv7]
  exact ⟨hTt7, hD7, hO7, hS7, hM7, hV7⟩

set_option maxHeartbeats 3200000 in
/-- A delete's bitmap into the full leaf X (D + 1) at the end of the key access
path (`PathOK` from the space root, D + 1 ≥ 1): the leaf is replaced by its last
version without cv and splits, with the cascade above. It keeps `TakeJ2` and B
at most the next id, from `PutInv`, its global parts and the walk's ranges, the
leaf's klong of cv naming no node (the key's value). -/
theorem writerWP_appendDeleteKlong_full_j2 (c : Ctx) (base : View BVal) (B : NodeId) (hpos : 0 < c.i)
    (w : W) (hI : PutInv c base w) (hG : PutInvG c base w)
    (hRO : RangeOrder (wNode c.p base w) c.i w.top.rootKey)
    (hJ : TakeJ2 c base B w) (hBn : B ≤ w.next) (hsa2 : 2 ≤ c.p.splitAbove)
    (D : Nat) (X : Nat → NodeId) (K : Nat → Nat) (Nn : Nat → KNode) (hP : PathOK c w (D + 1) X K Nn)
    (cv : Nat) (hnl : (Nn (D + 1)).leaf = true)
    (hne : bitsUnion (Nn (D + 1)).lastBitmap ((Nn (D + 1)).bitsOf cv) ≠ (Nn (D + 1)).lastBitmap)
    (hfull : ¬ DelRoom c cv (Nn (D + 1)))
    (hcvN : ∀ y, (cv, y) ∈ (Nn (D + 1)).liveAt c.i → wNode c.p base w y = none) :
    WriterWP (appendDeleteKlong (X (D + 1)) (D + 1) cv) c w
      (fun _ v => TakeJ2 c base B v ∧ B ≤ v.next) := by
  have hP' := hP
  obtain ⟨hX, hK, hS2, hlink, h0⟩ := hP'
  have hT := hI.tree
  have hreach := pathOK_reach c base w (D + 1) X K Nn hP
  have hdist := pathOK_dist c base w (D + 1) X K Nn hP hT
  have hw : ∀ j, j ≤ D + 1 → wNode c.p base w (X j) = some (Nn j) := by
    intro j hj
    obtain ⟨a, b⟩ := hS2 j hj
    simp only [wNode, b, Bool.false_eq_true, ↓reduceIte, a]
  have hO := ordG_of_rangeOrder c _ _ hRO hI.times
  have hord : ∀ i, 0 < i → i ≤ D → ChainOrd c K Nn i :=
    fun i h1 h2 => chainOrd_of_ordG c base w (D + 1) X K Nn hP hO i h1 (by omega)
  generalize hn : Nn (D + 1) = n at hnl hne hfull hcvN
  have hnt : ∀ s, Klong.time s ∈ n.ks → s ≤ c.i := hI.times _ _ (hn ▸ hw (D + 1) (Nat.le_refl _))
  have hlk : w.nodes.lookup (X (D + 1)) = some n := by rw [← hn]; exact (hS2 (D + 1) (Nat.le_refl _)).1
  obtain ⟨hleq, hlt, _⟩ := delLast_facts n c.i cv
  generalize hU : bitsUnion n.lastBitmap (n.bitsOf cv) = U at hne hfull hleq hlt
  generalize hlast : n.lastVersionGivenDel c.i U = last at hleq hlt
  have hdl : ∀ c', last.live.lookup c' = if c' == cv then none else n.live.lookup c' := by
    intro c'; rw [← hlast, ← hU]; exact KNode.delete_live_lookup n c.i cv c'
  have hiff := liveAt_iff_of_delete_lookup n last c.i cv hnt hlt hdl
  have hleq' : (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode) = last := by rw [hn]; exact hleq
  obtain ⟨pairs, hks, hsorted⟩ := n.lastVersionGivenDel_order c.i U
  rw [hlast] at hks
  have hks' : last.ks = newKlongs c.i pairs := by rw [hks]; rfl
  have hsize : last.size = pairs.length + 1 := by simp [KNode.size, hks', newKlongs]
  have hlive : (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode).live = pairs := by
    rw [hks']; exact KNode.live_newKlongs_sorted _ _ _ hsorted
  have hsub : ∀ c' z, (c', z) ∈ last.liveAt c.i → (c', z) ∈ n.liveAt c.i :=
    fun c' z h => ((hiff c' z).mp h).1
  -- the handleFull of the last version, for both kinds
  have hmain : ∀ (compact : Bool) (s : String),
      WriterWP (handleFull (D + 1) (X (D + 1)) last compact) c ({ w with trail := s :: w.trail } : W)
        (fun _ v => TakeJ2 c base B v ∧ B ≤ v.next) := by
    intro compact s
    refine writerWP_handleFull_last_j2 2 (Nat.le_refl _) c base B hpos ({ w with trail := s :: w.trail } : W)
      hJ hBn
      (by
        intro y hy
        obtain ⟨e, he, rfl⟩ := List.mem_map.mp hy
        have := hI.ids.2.2.2.1 _ he
        simpa using this)
      D X K Nn (fun i _ hi => hX i hi) (fun i h1 hi => hK i h1 hi) (fun i h1 hi => hlink i h1 hi)
      (fun i h1 hi hNR hql' c' z hz hpos' =>
        rangeG_of_rangeOrder c _ _ hRO hI.times (X (i - 1)) (Nn (i - 1)) (X i) (Nn i) (K i)
          (hreach (i - 1) (by omega)) (hw (i - 1) (by omega)) hql' (hlink i h1 (by omega))
          (hw i (by omega)) hNR c' z hz hpos')
      (fun i _ hi hNR hsp => lenG_of_splitAbove c _ _ hsa2 (X i) (Nn i) (hreach i (by omega))
        (hw i (by omega)) hNR hsp)
      (fun i _ hi => hI.wf _ _ (hw i hi)) (fun i _ hi => hI.times _ _ (hw i hi))
      (fun i i' _ hi _ hi' he => hdist i i' hi hi' he)
      (by
        intro i _ hi hNR hsp
        rcases Nat.eq_zero_or_pos i with h | h
        · exact Or.inl h
        · exact Or.inr ⟨h, Or.inr (fun _ i' h1 h2 => hord i' h1 (by omega))⟩)
      hord last compact (by rw [hks']; exact klongsWf_newKlongs c.i pairs) hlt
      (by
        have hlastEq : last = ⟨n.leaf, newKlongs c.i pairs⟩ := by rw [← hks', hleq]
        rw [hleq', hlastEq, KNode.lastVersion_newKlongs_sorted _ _ _ hsorted])
      (by intro h; rw [hlive]; omega)
      (by
        intro _ hql c' z hz hpos'
        rw [hleq'] at hz
        have hz' : (c', z) ∈ last.liveAt c.i := by rw [KNode.liveAt_of_times _ c.i hlt]; exact hz
        have hzn := hsub c' z hz'
        obtain ⟨hP1, hP2⟩ := mrg_child_range (wNode c.p base w) c.i w.top.rootKey hRO (X D) (Nn D)
          (tReach_reachS _ _ _ _ (hreach D (by omega))) (hw D (by omega)) hql (K (D + 1)) (X (D + 1)) n
          (by have := hlink (D + 1) (by omega) (Nat.le_refl _); simpa using this)
          (by rw [← hn]; exact hw (D + 1) (Nat.le_refl _))
        refine ⟨?_, ?_⟩
        · rcases Nat.eq_zero_or_pos (K (D + 1)) with hk0 | hk0
          · omega
          · exact (hP1 c' z hzn).1 hnl hk0
        · intro c'' z' hz2 hlt2
          exact hP2 c'' z' (by rw [KNode.liveAt_of_times _ c.i (hI.times _ _ (hw D (by omega)))]; exact hz2)
            hlt2 c' z hzn)
      (fun _ => Or.inr (fun _ i' h1 h2 => hord i' h1 (by omega)))
      ⟨pairs, hks', List.pairwise_map.mpr (hsorted.imp (by intro a b hab; omega))⟩
      (fun _ hql => by
        rw [hn]
        exact lastOrd_raw_of_live c (wNode c.p base w) w.top.rootKey hRO (X D) (Nn D) (K (D + 1))
          (X (D + 1)) n (hreach D (by omega)) (hw D (by omega)) hql
          (by have := hlink (D + 1) (by omega) (Nat.le_refl _); simpa using this)
          (by rw [← hn]; exact hw (D + 1) (Nat.le_refl _)) hnt last
          (by
            intro c' z hz
            rw [hleq] at hz
            have hz' : (c', z) ∈ last.liveAt c.i := by rw [KNode.liveAt_of_times _ c.i hlt]; exact hz
            exact ⟨z, by rw [← KNode.liveAt_of_times _ c.i hnt]; exact hsub c' z hz'⟩))
      (fun i _ hi => hS2 i hi) hT (fun i _ hi => hreach i hi)
      (by
        intro z hz
        change w.next ≤ z at hz
        refine ⟨?_, ?_, (hI.fresh z hz).1⟩
        · cases h' : w.nodes.lookup z with
          | none => rfl
          | some _ => have := hI.ids.1 z (by rw [h']; rfl); omega
        · cases h' : w.taken.contains z with
          | false => rfl
          | true => have := hI.ids.2.2.1 z h'; omega)
      (fun u c' z ⟨un, hun, hl⟩ => hG.links u un c' z hun hl)
      h0.symm hI.wf
      (by
        rw [hleq']
        exact treeOK_of_node_shrink (wNode c.p base w) _ c.i _ (X (D + 1)) n last hT
          (by rw [← hn]; exact hw (D + 1) (Nat.le_refl _)) (updN_self _ _ _)
          (fun y hy => by simp only [updN, hy, ↓reduceIte]; rfl) hsub)
      (by
        intro c' z hz
        rw [hleq'] at hz
        exact hG.links _ n c' z (by rw [← hn]; exact hw (D + 1) (Nat.le_refl _)) (hsub c' z hz))
      (by
        intro cc u hm
        rw [hn] at hm
        rw [hleq']
        by_cases hc : cc = cv
        · rw [hc] at hm; exact Or.inr (hcvN u hm)
        · exact Or.inl ⟨cc, (hiff cc u).mpr ⟨hm, hc⟩⟩)
  -- the bitmap's branches: a full leaf is replaced by its last version
  unfold appendDeleteKlong
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known _ n c w hlk]
  split
  · exact writerWP_throw _ _ _ _
  · have hno : (bitsUnion n.lastBitmap (n.bitsOf cv) == n.lastBitmap) = false := by
      rw [hU]; simpa using hne
    rw [hU] at hno
    simp only [hno, hU, hlast, Bool.not_false, ↓reduceIte]
    have hhf : ∀ (compact : Bool) (s : String), WriterWP (do
        note s
        handleFull (D + 1) (X (D + 1)) last compact
        pure false) c w (fun _ v => TakeJ2 c base B v ∧ B ≤ v.next) := by
      intro compact s
      simp only [note, writerWP_bind, writerWP_modify]
      refine writerWP_mono (hmain compact s) ?_
      intro _ v hv
      simp only [writerWP_pure]; exact hv
    have hU' : bitsUnion n.lastBitmap (n.bitsOf cv) = U := hU
    apply writerWP_ite_cases
    · intro htd
      apply writerWP_ite_cases
      · intro _; exact hhf true _
      · intro hdead
        exfalso; apply hfull; left
        have hdead' : deadOver c.p (n.setAt (n.size - 1) (Klong.del U)) = false := by simpa using hdead
        rw [← hU'] at hdead'
        cases hgl : n.ks.getLast? with
        | none => simp [hgl] at htd
        | some k =>
          cases k with
          | del old =>
            simp [hgl] at htd
            exact ⟨⟨old, rfl⟩, htd, hdead'⟩
          | time t => simp [hgl] at htd
          | key a y => simp [hgl] at htd
    · intro htd
      apply writerWP_ite_cases
      · intro hroom
        apply writerWP_ite_cases
        · intro _; exact hhf true _
        · intro hdead
          exfalso; apply hfull; right
          refine ⟨?_, hroom, ?_⟩
          · rintro ⟨⟨old, hold⟩, hlt'⟩
            apply htd
            simp [hold, hlt']
          · rw [hU']; simpa using hdead
      · intro _; exact hhf false _

end SIS.Tree
