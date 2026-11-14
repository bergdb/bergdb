/-
The take-back's facts through a full node's cascade with the nodes of the
transaction's time reached in the tree with the node's last version (bergdb
024-12, `UpCascJ2OKF3`): `writerWP_handleFull_root_j2` and
`writerWP_handleFull_last_j2` with `TakeJ2`'s node facts before and `hTU`
instead of `TakeJ2` and the node's kept children.
-/
import SIS.Tree.DelStepsCascRoot
import SIS.Tree.DelStepsBookK
import SIS.Tree.DelStepsUpStop
import SIS.Tree.DelStepsCascF3
import SIS.Tree.TakeDelStepsF4
import SIS.Tree.TakeFullLast
import SIS.Tree.TakeRunQF4

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

set_option maxHeartbeats 3200000 in
/-- `writerWP_handleFull_root_j2` with `TakeJ2`'s node facts before and the nodes
of the transaction's time reached in the tree with the root's last version. -/
theorem writerWP_handleFull_root_j2U (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (B : NodeId) (hpos : 0 < c.i) (L : NodeId) (n last : KNode) (compact : Bool)
    (w : W)
    (hJ : DeadLiveN (wNode c.p base w) c.i B (w.vals.map (·.1)) ∧ OldBelowN (wNode c.p base w) c.i B ∧
      OldStartN (wNode c.p base w) c.i B ∧ MadeStartN (wNode c.p base w) c.i B ∧
      ValsNoNodeN (wNode c.p base w) (w.vals.map (·.1)))
    (hBn : B ≤ w.next)
    (hvnx : ∀ y ∈ w.vals.map (·.1), y < w.next)
    (hT : TreeOK (wNode c.p base w) c.i w.top.rootKey)
    (hlwf : klongsWf last.ks = true) (hlt : ∀ s, Klong.time s ∈ last.ks → s ≤ c.i)
    (hlastV : (⟨n.leaf, last.ks⟩ : KNode).lastVersion c.i = last)
    (hlen2 : c.p.splitAbove < last.size → 2 ≤ (⟨n.leaf, last.ks⟩ : KNode).live.length)
    (hpairs : ∃ pairs, last.ks = newKlongs c.i pairs ∧ (pairs.map Prod.fst).Nodup)
    (hlk : w.nodes.lookup L = some n) (htk : w.taken.contains L = false)
    (hrk : w.top.rootKey = L)
    (hS5 : ∀ z, w.next ≤ z → w.nodes.lookup z = none ∧ w.taken.contains z = false ∧
      knodeOf c.p base z = none)
    (hS6 : ∀ u c' z, TLink (wNode c.p base w) c.i u c' z → z < w.next)
    (hW : ∀ z zn, wNode c.p base w z = some zn → klongsWf zn.ks = true)
    (hV : TreeOK (updN (wNode c.p base w) L ⟨n.leaf, last.ks⟩) c.i w.top.rootKey)
    (hvx : ∀ c' z, (c', z) ∈ (⟨n.leaf, last.ks⟩ : KNode).liveAt c.i → z < w.next)
    (hnwf : klongsWf n.ks = true) (hnt : ∀ s, Klong.time s ∈ n.ks → s ≤ c.i)
    (hTU : ∀ q qn, wNode c.p base w q = some qn → Klong.time c.i ∈ qn.ks →
      TReach (updN (wNode c.p base w) L ⟨n.leaf, last.ks⟩) c.i w.top.rootKey q) :
    WriterWP (handleFullWith rootUp 0 L [] last compact) c w
      (fun _ w' => TakeJ2 c base B w' ∧ B ≤ w'.next) := by
  have hLn : L < w.next := by
    rcases Nat.lt_or_ge L w.next with h | h
    · exact h
    · rw [(hS5 L h).1] at hlk; cases hlk
  have hwL : wNode c.p base w L = some n := by
    simp only [wNode, htk, Bool.false_eq_true, ↓reduceIte, hlk]
  have hlevel := writerWP_handleFull_rootVF2 2 (Nat.le_refl _) c base hvc rootUp L n last compact hlwf hlt
    hlastV hlen2 w hlk htk hrk hS5 hS6 hW hV hvx
  have hshape := writerWP_handleFull_rootShape c rootUp L n last compact (fun _ => L) (fun _ => 0)
    (fun _ => n) rfl rfl hpairs hlastV hlen2 w hlk hLn (fun z hz => (hS5 z hz).1)
  have hcache := @state_handleFullWith_compact (cachedFromInvariant w) rootUp 0 L [] last compact
    (fun q more => @keepsState_rootUp (cachedFromInvariant w) q more) c w (cachedFrom_refl _ c)
  have hnext := @state_handleFullWith_compact (nextFromInvariant w) rootUp 0 L [] last compact
    (fun q more => @keepsState_rootUp (nextFromInvariant w) q more) c w (Nat.le_refl _)
  refine writerWP_mono (writerWP_and (writerWP_and (writerWP_and hlevel hshape) hcache) hnext) ?_
  rintro _ w7 ⟨⟨⟨⟨_, ht7, hv7, _, _, _, _, hRB8, hRB9, hRB10, _⟩, hSP7, _⟩, hca7⟩, hn7⟩
  have hN6 : ∀ i, 0 ≤ i → i ≤ 0 → wNode c.p base w ((fun _ => L) i) = some ((fun _ => n) i) :=
    fun _ _ _ => hwL
  obtain ⟨_, hfr7, _, hsh⟩ := hSP7
  have hN76 : ∀ z, z < w.next → (∀ i, 0 ≤ i → i ≤ 0 → z ≠ (fun _ => L) i) →
      wNode c.p base w7 z = wNode c.p base w z := by
    intro z hz hnc
    simp only [wNode, ht7, hfr7 z hz hnc]
  obtain ⟨hD7, hO7, hS7, hM7, hV7⟩ := j2rest_cascade2 (wNode c.p base w) (wNode c.p base w7) c.i
    w.top.rootKey B (w.vals.map (·.1)) (fun _ => L) (fun _ => n) 0 0 w.next hpos hT hJ.1 hJ.2.1
    hJ.2.2.1 hJ.2.2.2.1 hJ.2.2.2.2 hN6 (fun _ _ _ => hnwf) (fun _ _ _ => hnt)
    (fun _ _ _ => by rw [hrk]; exact TReach.root) hvnx hN76
    (by
      intro z zn hz hz'
      have htz : w7.taken.contains z = false := by
        rw [ht7]
        rcases hz' with h | ⟨i, _, _, hzi⟩
        · exact (hS5 z h).2.1
        · rw [hzi]; exact htk
      have hlk7 : w7.nodes.lookup z = some zn := by
        unfold wNode at hz
        rw [htz] at hz
        simp only [Bool.false_eq_true, ↓reduceIte] at hz
        cases hl : w7.nodes.lookup z with
        | some m => rw [hl] at hz; exact hz
        | none =>
          exfalso
          rw [hl] at hz
          rcases hz' with h | ⟨i, _, _, hzi⟩
          · rw [(hS5 z h).2.2] at hz; cases hz
          · skip
            have := hca7 L (by rw [hlk]; rfl)
            rw [← hzi, hl] at this; cases this
      exact cascadeShapeJ2_of c (wNode c.p base w) B _ (fun _ => L) (fun _ => 0) (fun _ => n) 0 0 [] _
        hJ.2.2.1 hJ.2.2.2.1 hN6 (fun _ _ _ => hnt) hBn (by simp) (by simp) z zn hz' (hsh z zn hlk7 hz'))
  -- (B): a node of the transaction's time is reached
  have hTt7 : TtReachedN (wNode c.p base w7) c.i w7.top.rootKey := by
    intro q qn hq hm
    by_cases hqL : q = L
    · subst hqL
      rcases hRB9 with h | ⟨_, h, _⟩
      · exact h
      · exfalso
        rw [h] at hq
        cases hq
        exact time_not_mem_toPrev n c.i hpos hm
    by_cases hqn : w.next ≤ q
    · refine hRB10 q hqn ?_
      have htz : w7.taken.contains q = false := by rw [ht7]; exact (hS5 q hqn).2.1
      unfold wNode at hq
      rw [htz] at hq
      simp only [Bool.false_eq_true, ↓reduceIte] at hq
      cases hl : w7.nodes.lookup q with
      | some _ => rfl
      | none => rw [hl, (hS5 q hqn).2.2] at hq; cases hq
    rw [hN76 q (by omega) (fun _ _ _ => hqL)] at hq
    exact hRB8 q (hTU q qn hq hm) hqL
  refine ⟨?_, Nat.le_trans hBn hn7⟩
  unfold TakeJ2
  rw [hv7]
  exact ⟨hTt7, hD7, hO7, hS7, hM7, hV7⟩

set_option maxHeartbeats 3200000 in
/-- `writerWP_handleFull_last_j2` with `TakeJ2`'s node facts before and the nodes of
the transaction's time reached in the tree with the node's last version. -/
theorem writerWP_handleFull_last_j2U (fuelR : Nat) (hfR : 2 ≤ fuelR) (c : Ctx) (base : View BVal)
    (B : NodeId) (hpos : 0 < c.i) (w : W)
    (hJ : DeadLiveN (wNode c.p base w) c.i B (w.vals.map (·.1)) ∧ OldBelowN (wNode c.p base w) c.i B ∧
      OldStartN (wNode c.p base w) c.i B ∧ MadeStartN (wNode c.p base w) c.i B ∧
      ValsNoNodeN (wNode c.p base w) (w.vals.map (·.1)))
    (hBn : B ≤ w.next)
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
    (hTU : ∀ q qn, wNode c.p base w q = some qn → Klong.time c.i ∈ qn.ks →
      TReach (updN (wNode c.p base w) (X (D + 1)) (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode)) c.i w.top.rootKey q) :
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
    w.top.rootKey B (w.vals.map (·.1)) X Nn 0 (D + 1) w.next hpos hS3 hJ.1 hJ.2.1 hJ.2.2.1
    hJ.2.2.2.1 hJ.2.2.2.2 hN6 hwf htimes hS4 hvnx hN76
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
      exact cascadeShapeJ2_of c (wNode c.p base w) B _ X K Nn 0 (D + 1) [] _ hJ.2.2.1 hJ.2.2.2.1 hN6
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
    exact hRB1' q (hTU q qn hq hm) hnc
  refine ⟨?_, Nat.le_trans hBn hn7⟩
  unfold TakeJ2
  rw [hv7]
  exact ⟨hTt7, hD7, hO7, hS7, hM7, hV7⟩

set_option maxHeartbeats 6400000 in
/-- The take-back's facts through the stop node's bitmap into a full space root
(`UpCascJ2OKF3` at stop 0): from the state after the upward loop as a tree
(`UpUnlinkOK`), its links and klongs, `TakeJ2` keeps with B at most the next id:
the node facts after the loop (`j2rest_up` with the stop node as it is), the
nodes of the transaction's time reached in the tree with the root's last version
(`ttReachedN_up`), the root's split (`writerWP_handleFull_root_j2U`). -/
theorem writerWP_upCasc_root_j2 (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (hsa2 : 2 ≤ c.p.splitAbove) (B : NodeId) (hpos : 0 < c.i)
    (w w3 : W) (X : Nat → NodeId) (Nn : Nat → KNode) (K : Nat → Nat) (depth : Nat) (w2 v : W) (S : KNode)
    (hI : PutInv c base w) (hr03 : ReadsAs c.p base w w3) (hJw : TakeJ2 c base B w) (hBn : B ≤ w.next)
    (hkidsw : ∀ c' z, (c', z) ∈ (Nn depth).liveAt c.i → wNode c.p base w z = none)
    (hlkX : ∀ i, i ≤ depth → w3.nodes.lookup (X i) = some (Nn i))
    (hXN : ∀ i, i ≤ depth → wNode c.p base w (X i) = some (Nn i))
    (hlinkK : ∀ i, 0 < i → i ≤ depth → (K i, X i) ∈ (Nn (i - 1)).liveAt c.i)
    (hdepth : 0 < depth)
    (hbetween : ∀ i, 0 < i → i < depth →
      (Nn i).allKeysIn (bitsUnion (Nn i).lastBitmap ((Nn i).bitsOf (K (i + 1)))) = true)
    (hX0 : X 0 = w.top.rootKey)
    (hLE : UpLoopEnd c B X Nn depth 0 w3 w2 S)
    (hv : v = w2 ∨ ∃ s, v = { w2 with trail := s :: w2.trail })
    (hfull : ¬ DelRoom c (K 1) S)
    (hT2 : TreeOK (wNode c.p base w2) c.i w2.top.rootKey)
    (hlinks2 : ∀ u c' z, TLink (wNode c.p base w2) c.i u c' z → z < w2.next)
    (hwf2 : ∀ z zn, wNode c.p base w2 z = some zn → klongsWf zn.ks = true) :
    WriterWP (appendDeleteKlong (X 0) 0 (K 1)) c v
      (fun _ w' => TakeJ2 c base B w' ∧ B ≤ w'.next) := by
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
  have hI3 := putInv_of_readsAs c base w w3 hI hr03
  have htk3 : ∀ i, i ≤ depth → w3.taken.contains (X i) = false := fun i hi => by
    rw [hr03.2.2.1]; exact hI.untaken _ (tReach_reachS _ _ _ _ (hreach i hi))
  have hT3 : TreeOK (wNode c.p base w3) c.i w3.top.rootKey := by rw [hr03.1, hr03.2.1]; exact hT
  have hreach3 : ∀ i, i ≤ depth → TReach (wNode c.p base w3) c.i w3.top.rootKey (X i) := fun i hi => by
    rw [hr03.1, hr03.2.1]; exact hreach i hi
  have hJ3 : TakeJ2 c base B w3 := takeJ2_of_readsAs c base B w w3 hJw hr03
  obtain ⟨h2t, h2top, h2v, _, _, h2nx, h2n, hSl, hS, hSR, hSF', hfate2, hfateJ2⟩ := hLE
  have hvn : v.nodes = w2.nodes := by rcases hv with rfl | ⟨s, rfl⟩ <;> rfl
  have hvt : v.taken = w2.taken := by rcases hv with rfl | ⟨s, rfl⟩ <;> rfl
  have hvtop : v.top = w2.top := by rcases hv with rfl | ⟨s, rfl⟩ <;> rfl
  have hvv : v.vals = w2.vals := by rcases hv with rfl | ⟨s, rfl⟩ <;> rfl
  have hvnx : v.next = w2.next := by rcases hv with rfl | ⟨s, rfl⟩ <;> rfl
  have hwv : wNode c.p base v = wNode c.p base w2 := by
    funext z; simp only [wNode, hvn, hvt]
  have hXs : ∀ k, 0 < k → k ≤ depth → X 0 ≠ X k :=
    fun k h1 h2 he => by have := hdist 0 k (by omega) h2 he; omega
  have hst_t : ∀ s', Klong.time s' ∈ (Nn 0).ks → s' ≤ c.i := hI.times _ _ (hXN 0 (by omega))
  have hsx : (K 1, X 1) ∈ (Nn 0).liveAt c.i := by
    have := hlinkK 1 (by omega) hdepth; simpa using this
  have hneS : bitsUnion (Nn 0).lastBitmap ((Nn 0).bitsOf (K 1)) ≠ (Nn 0).lastBitmap := by
    apply KNode.delete_bitmap_changes_of_live
    have hsx' := hsx
    rw [KNode.liveAt_of_times _ c.i hst_t] at hsx'
    exact List.mem_map.mpr ⟨_, hsx', rfl⟩
  have hswf : klongsWf (Nn 0).ks = true := hI.wf _ _ (hXN 0 (by omega))
  have hu : ∀ c', (c', X 1) ∈ (Nn 0).liveAt c.i → c' = K 1 := by
    intro c' h
    exact (hT.oneLink _ _ _ _ _ (hreach 0 (by omega)) (hreach 0 (by omega)) ⟨_, hXN 0 (by omega), h⟩
      ⟨_, hXN 0 (by omega), hsx⟩).2
  have hSf : S.shapeOf = (Nn 0).shapeOf ∧ S.leaf = (Nn 0).leaf ∧ klongsWf S.ks = true ∧
      (∀ s, Klong.time s ∈ S.ks → s ≤ c.i) ∧
      ∀ c' z, ((c', z) ∈ S.liveAt c.i ∧ c' ≠ K 1) ↔ ((c', z) ∈ (Nn 0).liveAt c.i ∧ c' ≠ K 1) := by
    rcases hS with rfl | ⟨ti, dst, rfl⟩
    · exact ⟨rfl, rfl, hswf, hst_t, fun _ _ => Iff.rfl⟩
    · exact ⟨KNode.retarget_shapeOf _ _ _ _, rfl, by rw [klongsWf_retargetKlongs]; exact hswf,
        KNode.retarget_times _ _ _ _ _ hst_t, KNode.retarget_liveAt_ne _ _ _ _ _ _ hu⟩
  obtain ⟨hSsh, hSleaf, hSwf, hSt, hSlive⟩ := hSf
  have hneS' : bitsUnion S.lastBitmap (S.bitsOf (K 1)) ≠ S.lastBitmap := by
    rw [KNode.lastBitmap_of_shapeOf hSsh, KNode.bitsOf_of_shapeOf hSsh]; exact hneS
  have hlkv : v.nodes.lookup (X 0) = some S := by rw [hvn]; exact hSl
  have htk2 : w2.taken.contains (X 0) = false := by rw [h2t _ hXs]; exact htk3 0 (by omega)
  have hagree2 : ∀ u, u ≠ X 0 → (∀ i, 0 < i → i ≤ depth → u ≠ X i) →
      wNode c.p base w2 u = wNode c.p base w3 u := fun u hus hnc => by
    simp only [wNode, h2t u hnc, h2n u hus hnc]
  have hS2w : wNode c.p base w2 (X 0) = some S := by
    simp only [wNode, htk2, Bool.false_eq_true, ↓reduceIte, hSl]
  have hone : ∀ i, 0 < i → i < depth → ∀ c' z, (c', z) ∈ (Nn i).liveAt c.i → z = X (i + 1) := by
    intro i h1 h2 c' z hm
    have ht := hI.times _ _ (hXN i (by omega))
    have hm' : (c', z) ∈ (Nn i).live := by rw [← KNode.liveAt_of_times _ c.i ht]; exact hm
    have hc := allKeysIn_live_cv (Nn i) (K (i + 1)) (hbetween i h1 h2) c' z hm'
    have hl := hlinkK (i + 1) (by omega) (by omega)
    rw [show i + 1 - 1 = i by omega] at hl
    rw [KNode.liveAt_of_times _ c.i ht] at hl
    have hnd := KNode.live_keys_nodup (Nn i)
    have e1 := lookup_some_of_mem hnd hm'
    have e2 := lookup_some_of_mem hnd hl
    rw [hc] at e1
    rw [e1] at e2
    exact Option.some.inj e2
  -- the node facts after the loop
  have hrest2 := j2rest_up (wNode c.p base w3) (wNode c.p base w2) c.i B (w3.vals.map (·.1)) X Nn 0 depth
    (K 1) hdepth hpos hJ3.2.1 hJ3.2.2.1 hJ3.2.2.2.1 hJ3.2.2.2.2.1 hJ3.2.2.2.2.2 (fun i _ hi => hN3 i hi)
    (fun i i' _ hi _ hi' he => hdist i i' hi hi' he)
    (by
      intro k h1 h2
      obtain ⟨hm, hu'⟩ := hfateJ2 k h1 h2
      refine ⟨fun hf => by simp only [wNode, hm hf, ↓reduceIte], fun hf => ?_⟩
      obtain ⟨ht0, S0, hS0, hl0⟩ := hu' hf
      exact ⟨S0, hS0, by simp only [wNode, ht0, Bool.false_eq_true, ↓reduceIte, hl0]⟩)
    hswf hst_t hsx S S (fun _ => False) hSR hSF' hS2w rfl (fun s h => h)
    (fun i c' y h => Or.inl h) (fun y h => h.elim)
    (fun c' y hm hc => ⟨c', ((hSlive c' y).mpr ⟨hm, hc⟩).1⟩)
    (fun hl => ⟨hl, fun i c' hL _ => hL⟩) hagree2
  refine writerWP_appendDeleteKlong_full_of (X 0) 0 (K 1) S c v hlkv hneS' hfull _ ?_
  intro compact s
  generalize hlast : S.lastVersionGivenDel c.i (bitsUnion S.lastBitmap (S.bitsOf (K 1))) = last
  obtain ⟨hleq, hlwf, hlt, hlastV, hlen2, hpairs, hiff, _⟩ := delLast_split_facts c S (K 1) hsa2 hSt last hlast
  have hliveL : ∀ c' z, (c', z) ∈ (⟨S.leaf, last.ks⟩ : KNode).liveAt c.i ↔
      (c', z) ∈ (Nn 0).liveAt c.i ∧ c' ≠ K 1 := by
    intro c' z; rw [hleq, hiff c' z]; exact hSlive c' z
  have hlk' : ({ v with trail := s :: v.trail } : W).nodes.lookup (X 0) = some S := hlkv
  have htk' : ({ v with trail := s :: v.trail } : W).taken.contains (X 0) = false := by
    show v.taken.contains _ = false; rw [hvt]; exact htk2
  have hroot' : ({ v with trail := s :: v.trail } : W).top.rootKey = w3.top.rootKey := by
    show v.top.rootKey = _; rw [hvtop, h2top]
  have hrk' : ({ v with trail := s :: v.trail } : W).top.rootKey = X 0 := by
    rw [hroot', hr03.2.1, hX0]
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
      rw [hvn, h2n z (hzX 0 (by omega)) (fun i _ hi => hzX i hi)]
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
  have hagreeV : ∀ u, u ≠ X 0 → (∀ i, 0 < i → i ≤ depth → u ≠ X i) →
      updN (wNode c.p base ({ v with trail := s :: v.trail } : W)) (X 0) ⟨S.leaf, last.ks⟩ u =
        wNode c.p base w3 u := fun u hus hnc => by
    rw [updN_ne _ _ _ _ hus, hwv']; exact hagree2 u hus hnc
  have hsnV : updN (wNode c.p base ({ v with trail := s :: v.trail } : W)) (X 0) ⟨S.leaf, last.ks⟩ (X 0) =
      some ⟨S.leaf, last.ks⟩ := updN_self _ _ _
  have hV : TreeOK (updN (wNode c.p base ({ v with trail := s :: v.trail } : W)) (X 0) ⟨S.leaf, last.ks⟩)
      c.i ({ v with trail := s :: v.trail } : W).top.rootKey := by
    rw [hroot']
    exact treeOK_up_tr (wNode c.p base w3) _ c.i w3.top.rootKey X Nn K 0 depth hdepth hT3
      (hreach3 0 (by omega)) (fun i _ hi => hN3 i hi) (fun i h1 hi => hlinkK i h1 hi)
      (fun i i' _ hi _ hi' he => hdist i i' hi hi' he) hagreeV _ hsnV id
      (fun c' z h => ⟨c', ((hliveL c' z).mp h).1, ((hliveL c' z).mp h).2, rfl⟩)
  have hvx : ∀ c' z, (c', z) ∈ (⟨S.leaf, last.ks⟩ : KNode).liveAt c.i →
      z < ({ v with trail := s :: v.trail } : W).next := by
    intro c' z h
    rw [hnx', hr03.2.2.2.2]
    exact hI.links (X 0) (Nn 0) c' z (tReach_reachS _ _ _ _ (hreach 0 (by omega))) (hXN 0 (by omega))
      ((hliveL c' z).mp h).1
  -- the nodes of the transaction's time, reached in the tree with the root's last version
  have hTtV := ttReachedN_up (wNode c.p base w3)
    (updN (wNode c.p base ({ v with trail := s :: v.trail } : W)) (X 0) ⟨S.leaf, last.ks⟩) c.i
    w3.top.rootKey X Nn 0 depth hdepth (fun i _ hi => hN3 i hi) hone
    (fun c' z h => by rw [hr03.1]; exact hkidsw c' z h) _ hsnV
    (fun c' z hm hz => ⟨c', (hliveL c' z).mpr ⟨hm, fun hck => hz (by
      rw [hck] at hm; exact KNode.liveAt_fun _ _ _ _ _ hm hsx)⟩⟩)
    hagreeV hXs (hreach3 0 (by omega))
    (by
      intro k h1 h2 un hun
      rw [updN_ne _ _ _ _ (Ne.symm (hXs k h1 h2)), hwv'] at hun
      rcases hfate2 k h1 h2 with hf | ⟨S0, hS0, hnt0⟩
      · unfold wNode at hun; rw [hf] at hun; cases hun
      · have hkt : w2.taken.contains (X k) = false := by
          cases hc : w2.taken.contains (X k) with
          | false => rfl
          | true => unfold wNode at hun; rw [hc] at hun; cases hun
        simp only [wNode, hkt, Bool.false_eq_true, ↓reduceIte, hS0, Option.some.injEq] at hun
        rw [← hun]; exact hnt0)
    hJ3.1
  have hTU : ∀ q qn, wNode c.p base ({ v with trail := s :: v.trail } : W) q = some qn →
      Klong.time c.i ∈ qn.ks →
      TReach (updN (wNode c.p base ({ v with trail := s :: v.trail } : W)) (X 0) ⟨S.leaf, last.ks⟩) c.i
        ({ v with trail := s :: v.trail } : W).top.rootKey q := by
    intro q qn hq hm
    by_cases hq0 : q = X 0
    · rw [hq0, hrk']; exact TReach.root
    · rw [hroot']
      exact hTtV q qn (by rw [updN_ne _ _ _ _ hq0]; exact hq) hm
  have hvals2 : ({ v with trail := s :: v.trail } : W).vals = w3.vals := by
    show v.vals = _; rw [hvv, h2v]
  have hrest' : DeadLiveN (wNode c.p base ({ v with trail := s :: v.trail } : W)) c.i B
      (({ v with trail := s :: v.trail } : W).vals.map (·.1)) ∧
      OldBelowN (wNode c.p base ({ v with trail := s :: v.trail } : W)) c.i B ∧
      OldStartN (wNode c.p base ({ v with trail := s :: v.trail } : W)) c.i B ∧
      MadeStartN (wNode c.p base ({ v with trail := s :: v.trail } : W)) c.i B ∧
      ValsNoNodeN (wNode c.p base ({ v with trail := s :: v.trail } : W))
        (({ v with trail := s :: v.trail } : W).vals.map (·.1)) := by
    rw [hwv', hvals2]; exact hrest2
  exact writerWP_handleFull_root_j2U c base hvc B hpos (X 0) S last compact ({ v with trail := s :: v.trail } : W)
    hrest' (by rw [hnx', hr03.2.2.2.2]; exact hBn)
    (by
      intro y hy
      rw [hvals2] at hy
      rw [hnx']
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hy
      exact hI3.ids.2.2.2.1 e he)
    (by rw [hwv']; show TreeOK _ c.i v.top.rootKey; rw [hvtop]; exact hT2)
    hlwf hlt hlastV hlen2 hpairs hlk' htk' hrk' hS5 hS6 hW hV hvx hSwf hSt hTU

end SIS.Tree
