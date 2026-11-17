/-
The merge's tail where its parent goes `full` and splits in time below q (d ≥ 2)
with no hole after (bergdb 030-01, step 3's rest): a merge into two nodes, or into
one whose parent's last version still holds m live klongs or more. The copy's klong
goes up through `writerWP_appendKlongs_chainGL` whatever q's room (the cascade), as
for the delete's full leaf whose copy is filled (l4b's
`writerWP_handleFull_timeChain_live`, LiveAssembly2.lean), here on the merged tree.
The split is the no-hole tail's premise (`SplitStepOKX`). The rest is
`MergeTailFullRest9OK`.
-/
import SIS.Tree.LiveMergeRootSplit
import SIS.Tree.WriterTreeDelChain

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

set_option maxHeartbeats 8000000 in
/-- l4b's `writerWP_handleFull_timeChain_live` (LiveAssembly2.lean) on the tree V with
X (D + 1)'s node replaced by its last version (any node): from V's live counts (no
hole) the time split and its cascade keep them, and the nodes reached after were
reached in V or are new, not X (D + 1). -/
theorem writerWP_handleFull_timeChainV_live (c : Ctx) (base : View BVal)
    (path0 : List (Option Nat × NodeId)) (D : Nat) (X : Nat → NodeId) (K : Nat → Nat)
    (Nn : Nat → KNode) (last : KNode) (compact : Bool)
    (hX : ∀ i, i ≤ D + 1 → (path0[i]?).map (·.2) = some (X i))
    (hK : ∀ i, 0 < i → i ≤ D + 1 → path0[i]? = some (some (K i), X i))
    (hlinkK : ∀ i, 0 < i → i ≤ D + 1 → (K i, X i) ∈ (Nn (i - 1)).liveAt c.i)
    (hrange : ∀ i, 0 < i → i ≤ D → ¬ ChainRoom c (Nn i) → (Nn (i - 1)).leaf = false →
      ∀ c' z, (c', z) ∈ (Nn i).live → 0 < c' →
      K i ≤ c' ∧ ∀ c'' z', (c'', z') ∈ (Nn (i - 1)).live → K i < c'' → c' < c'')
    (hlen : ∀ i, 0 ≤ i → i ≤ D → ¬ ChainRoom c (Nn i) →
      c.p.splitAbove < ((Nn i).lastVersion c.i).size → 2 ≤ (Nn i).live.length)
    (hwf : ∀ i, i ≤ D + 1 → klongsWf (Nn i).ks = true)
    (htimes : ∀ i, i ≤ D + 1 → ∀ t, Klong.time t ∈ (Nn i).ks → t ≤ c.i)
    (hdist : ∀ i i', i ≤ D + 1 → i' ≤ D + 1 → X i = X i' → i = i')
    (hfirst : (Nn (D + 1)).firstTime ≠ some c.i)
    (hcs : (!compact && decide (last.size > c.p.splitAbove)) = false)
    (hmp : MergeParamsOK c.p)
    (w : W) (hS1 : w.path = path0)
    (hS2 : ∀ i, i ≤ D + 1 → w.nodes.lookup (X i) = some (Nn i) ∧ w.taken.contains (X i) = false)
    (hS3 : TreeOK (wNode c.p base w) c.i w.top.rootKey)
    (hS4 : ∀ i, i ≤ D + 1 → TReach (wNode c.p base w) c.i w.top.rootKey (X i))
    (hS5 : ∀ z, w.next ≤ z → w.nodes.lookup z = none ∧ w.taken.contains z = false ∧
      knodeOf c.p base z = none)
    (hS6 : ∀ u c' z, TLink (wNode c.p base w) c.i u c' z → z < w.next)
    (hR0 : w.top.rootKey = X 0)
    (hTV : TreeOK (updN (wNode c.p base w) (X (D + 1)) ⟨(Nn (D + 1)).leaf, last.ks⟩) c.i w.top.rootKey)
    (hlinksV : ∀ u c' z, TReach (updN (wNode c.p base w) (X (D + 1)) ⟨(Nn (D + 1)).leaf, last.ks⟩) c.i w.top.rootKey u → TLink (updN (wNode c.p base w) (X (D + 1)) ⟨(Nn (D + 1)).leaf, last.ks⟩) c.i u c' z → z < w.next)
    (hLV0 : LiveEdges c.p (updN (wNode c.p base w) (X (D + 1)) ⟨(Nn (D + 1)).leaf, last.ks⟩) c.i w.top.rootKey) :
    WriterWP (handleFullWith (fun q more => appendKlongs D q more) (D + 1) (X (D + 1)) [] last
      compact) c w (fun _ w' => LiveEdges c.p (wNode c.p base w') c.i w'.top.rootKey ∧
        (∀ z, TReach (wNode c.p base w') c.i w'.top.rootKey z →
          (TReach (updN (wNode c.p base w) (X (D + 1)) ⟨(Nn (D + 1)).leaf, last.ks⟩) c.i w.top.rootKey z ∨ w.next ≤ z) ∧ z ≠ X (D + 1)) ∧
        w'.taken = w.taken) := by
  have hchain := writerWP_appendKlongs_chainGL c base path0 0 D X K Nn
    (fun i _ h2 => hX i (by omega)) (fun i h1 h2 => hK i h1 (by omega))
    (fun i h1 h2 => hlinkK i h1 (by omega)) hrange hlen
    (fun i _ h2 => hwf i (by omega)) (fun i _ h2 => htimes i (by omega)) (Or.inr rfl)
    (fun i i' _ h2 _ h4 => hdist i i' (by omega) (by omega)) D (by omega)
  have h0D : 0 + D = D := Nat.zero_add D
  rw [h0D] at hchain
  obtain ⟨hlk, htk⟩ := hS2 (D + 1) (Nat.le_refl _)
  obtain ⟨hlq, htq⟩ := hS2 D (by omega)
  have hpq : (w.path[D]?).map (·.2) = some (X D) := by rw [hS1]; exact hX D (by omega)
  have hpk : w.path[D + 1]? = some (some (K (D + 1)), X (D + 1)) := by
    rw [hS1]; exact hK (D + 1) (by omega) (Nat.le_refl _)
  have hkl : (K (D + 1), X (D + 1)) ∈ (Nn D).liveAt c.i := by
    have := hlinkK (D + 1) (by omega) (Nat.le_refl _); simpa using this
  obtain ⟨hfree0, htk0, hbase0⟩ := hS5 w.next (Nat.le_refl _)
  have hwnext : wNode c.p base w w.next = none := by
    simp only [wNode, htk0, Bool.false_eq_true, ↓reduceIte, hfree0, hbase0]
  have hnoLink : ∀ z, w.next ≤ z → ∀ u c', ¬ TLink (wNode c.p base w) c.i u c' z := by
    intro z hz u c' hl; have := hS6 u c' z hl; omega
  have hyR : ∀ z, w.next ≤ z → ¬ TReach (wNode c.p base w) c.i w.top.rootKey z := by
    intro z hz
    have hwz : wNode c.p base w z = none := by
      obtain ⟨a, b, d⟩ := hS5 z hz
      simp only [wNode, b, Bool.false_eq_true, ↓reduceIte, a, d]
    exact not_reach_fresh _ c.i _ z hS3 hwz (fun u c' _ => hnoLink z hz u c')
  have hXlt : ∀ i, i ≤ D + 1 → X i < w.next := by
    intro i h2
    obtain ⟨hl, _⟩ := hS2 i h2
    rcases Nat.lt_or_ge (X i) w.next with hlt | hge
    · exact hlt
    · have := (hS5 (X i) hge).1
      rw [hl] at this; cases this
  have hqx : X D ≠ X (D + 1) := by
    intro h; have := hdist _ _ (by omega) (Nat.le_refl _) h; omega
  have hwq : wNode c.p base w (X D) = some (Nn D) := by
    simp only [wNode, htq, Bool.false_eq_true, ↓reduceIte, hlq]
  have hwx : wNode c.p base w (X (D + 1)) = some (Nn (D + 1)) := by
    simp only [wNode, htk, Bool.false_eq_true, ↓reduceIte, hlk]
  have hqwf := hwf D (by omega)
  have hqtimes := htimes D (by omega)
  have hXn1 : X (D + 1) ≠ w.next := by have := hXlt (D + 1) (Nat.le_refl _); omega
  have hQn1 : X D ≠ w.next := by have := hXlt D (by omega); omega
  have hXr : X (D + 1) ≠ w.top.rootKey := by
    intro h; rw [hR0] at h; have := hdist _ _ (Nat.le_refl _) (by omega) h; omega
  apply writerWP_handleFullWith_time_up_last' D (X (D + 1)) (X D) (Nn (D + 1)) (Nn D) (K (D + 1)) last
    compact c w hlk hlq hfirst hcs hpq hpk
  intro w1 h1n h1t h1top h1path h1next h1vals
  have hN1 : wNode c.p base w1 = updN (wNode c.p base w) w.next ⟨(Nn (D + 1)).leaf, last.ks⟩ := by
    funext z
    unfold wNode updN
    rw [h1t, h1n]
    by_cases hz : z = w.next
    · subst hz
      simp only [htk0, Bool.false_eq_true, ↓reduceIte, lookup_append_single_self _ _ _ hfree0]
    · simp only [hz, ↓reduceIte, lookup_append_single_ne _ _ _ _ hz]
  have hq1t := KNode.add_times (Nn D) c.i (.key (K (D + 1)) w.next) (fun s h => by cases h) hqtimes
  have hqlinks : ∀ c' z, (c', z) ∈ ([(K (D + 1), w.next)].foldl
      (fun n (cv, y) => n.add c.i (.key cv y)) (Nn D)).liveAt c.i →
      (c' = K (D + 1) ∧ z = w.next) ∨ (c' ≠ K (D + 1) ∧ (c', z) ∈ (Nn D).liveAt c.i) := by
    intro c' z h
    simp only [List.foldl_cons, List.foldl_nil] at h
    exact KNode.add_key_liveAt_mem _ c.i _ _ hqwf hqtimes c' z h
  have hq'l : ([(K (D + 1), w.next)].foldl
      (fun n (cv, y) => n.add c.i (.key cv y)) (Nn D)).leaf = (Nn D).leaf := by
    simp only [List.foldl_cons, List.foldl_nil, KNode.add_leaf]
  have hN'y : updN (wNode c.p base w1) (X D) ([(K (D + 1), w.next)].foldl
      (fun n (cv, y) => n.add c.i (.key cv y)) (Nn D)) w.next = some ⟨(Nn (D + 1)).leaf, last.ks⟩ := by
    rw [updN_ne _ _ _ _ hQn1.symm, hN1]; exact updN_self _ _ _
  have hoth : ∀ z, z ≠ X (D + 1) → z ≠ X D → z ≠ w.next →
      updN (wNode c.p base w1) (X D) ([(K (D + 1), w.next)].foldl
        (fun n (cv, y) => n.add c.i (.key cv y)) (Nn D)) z =
      updN (wNode c.p base w) (X (D + 1)) ⟨(Nn (D + 1)).leaf, last.ks⟩ z := by
    intro z hz1 hz2 hz3
    rw [updN_ne _ _ _ _ hz2, hN1, updN_ne _ _ _ _ hz3, updN_ne _ _ _ _ hz1]
  have hqV : TReach (updN (wNode c.p base w) (X (D + 1)) ⟨(Nn (D + 1)).leaf, last.ks⟩) c.i
      w.top.rootKey (X D) :=
    tReach_updN_parent _ c.i _ _ _ _ _ hS3 (hS4 D (by omega)) ⟨Nn D, hwq, hkl⟩
  have hqnV : updN (wNode c.p base w) (X (D + 1)) ⟨(Nn (D + 1)).leaf, last.ks⟩ (X D) = some (Nn D) := by
    rw [updN_ne _ _ _ _ hqx]; exact hwq
  have hfyV : updN (wNode c.p base w) (X (D + 1)) ⟨(Nn (D + 1)).leaf, last.ks⟩ w.next = none := by
    rw [updN_ne _ _ _ _ (Ne.symm hXn1)]; exact hwnext
  have hfreshV : ∀ u c', TReach (updN (wNode c.p base w) (X (D + 1)) ⟨(Nn (D + 1)).leaf, last.ks⟩) c.i w.top.rootKey u → ¬ TLink (updN (wNode c.p base w) (X (D + 1)) ⟨(Nn (D + 1)).leaf, last.ks⟩) c.i u c' w.next := by
    intro u c' hu hl
    have := hlinksV u c' w.next hu hl; omega
  have hxRV : TReach (updN (wNode c.p base w) (X (D + 1)) ⟨(Nn (D + 1)).leaf, last.ks⟩) c.i w.top.rootKey (X (D + 1)) := TReach.link hqV ⟨Nn D, hqnV, hkl⟩
  obtain ⟨hT1V, hR1V⟩ := treeOK_timeSplit_gen (updN (wNode c.p base w) (X (D + 1))
      ⟨(Nn (D + 1)).leaf, last.ks⟩)
    (updN (wNode c.p base w1) (X D) ([(K (D + 1), w.next)].foldl
      (fun n (cv, y) => n.add c.i (.key cv y)) (Nn D))) c.i w.top.rootKey (X D) (X (D + 1)) w.next
    (Nn D) ⟨(Nn (D + 1)).leaf, last.ks⟩ ⟨(Nn (D + 1)).leaf, last.ks⟩
    ([(K (D + 1), w.next)].foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn D)) (K (D + 1))
    hTV hqV hqnV hkl (updN_self _ _ _) (updN_self _ _ _) hqlinks hN'y (fun _ _ h => h) hoth hfyV hfreshV
  have hLV := liveEdgesX_timeSplit_gen c.p (fun _ => False) (updN (wNode c.p base w) (X (D + 1))
      ⟨(Nn (D + 1)).leaf, last.ks⟩)
    (updN (wNode c.p base w1) (X D) ([(K (D + 1), w.next)].foldl
      (fun n (cv, y) => n.add c.i (.key cv y)) (Nn D))) c.i w.top.rootKey (X D) (X (D + 1)) w.next
    (Nn D) ⟨(Nn (D + 1)).leaf, last.ks⟩ ⟨(Nn (D + 1)).leaf, last.ks⟩
    ([(K (D + 1), w.next)].foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn D)) (K (D + 1))
    hTV hqV hqnV hkl (updN_self _ _ _) (updN_self _ _ _) hqlinks hN'y (fun _ _ h => h) hoth hfyV hfreshV
    (fun h => h) (fun h => h) rfl (Nat.le_refl _) hq'l
    (addKeys_liveAt_length c.i [(K (D + 1), w.next)] (Nn D) hqwf hqtimes)
    ((liveEdgesX_false_iff _ _ _ _).mpr hLV0)
  have hpar := hchain w1 [(K (D + 1), w.next)] (Or.inl ⟨_, _, rfl⟩)
    (by
      intro q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rw [hq, h1next]; simp)
    (by rw [h1path, hS1])
    (by
      intro i _ h2
      obtain ⟨a, b⟩ := hS2 i (by omega)
      refine ⟨?_, by rw [h1t]; exact b⟩
      rw [h1n]
      have h1' : X i ≠ w.next := by have := hXlt i (by omega); omega
      rw [lookup_append_single_ne _ _ _ _ h1']; exact a)
    (by
      rw [hN1, h1top]
      exact treeOK_updN_unreach _ c.i _ _ _ hS3 (hyR w.next (Nat.le_refl _)))
    (by
      intro i _ h2
      rw [hN1, h1top]
      obtain ⟨a, ha⟩ := (hS4 i (by omega)).pathLen
      exact tReach_updN_of_short _ c.i _ _ _ a _ ha
        (fun b hb => absurd hb.reach (hyR w.next (Nat.le_refl _))))
    (by
      intro z hz
      rw [h1next] at hz
      obtain ⟨a, b, d⟩ := hS5 z (by omega)
      refine ⟨?_, by rw [h1t]; exact b, d⟩
      rw [h1n]
      have h1' : z ≠ w.next := by omega
      rw [lookup_append_single_ne _ _ _ _ h1']; exact a)
    (by
      intro u c' z hl
      rw [h1next]
      rw [hN1] at hl
      obtain ⟨m, hm, hc⟩ := hl
      by_cases hu1 : u = w.next
      · rw [hu1, updN_self] at hm
        simp only [Option.some.injEq] at hm
        subst hm
        have := hlinksV _ c' z hxRV ⟨_, updN_self _ _ _, hc⟩; omega
      · rw [updN_ne _ _ _ _ hu1] at hm
        have := hS6 u c' z ⟨m, hm, hc⟩; omega)
    (fun _ => by rw [h1top]; exact hR0)
    (by rw [h1top]; exact hT1V)
  refine writerWP_mono hpar ?_
  rintro _ w2 ⟨_, ⟨_, h2t, _, _, _⟩, h2frame, h2reach, h2live⟩
  have hlk2 : w2.nodes.lookup (X (D + 1)) = some (Nn (D + 1)) := by
    rw [h2frame _ (by have := hXlt (D + 1) (Nat.le_refl _); omega)
      (fun i _ h2 he => by have := hdist _ _ (Nat.le_refl _) (by omega) he; omega)]
    rw [h1n, lookup_append_single_ne _ _ _ _ hXn1]; exact hlk
  simp only [writerWP_bind]
  rw [writerWP_getNode_known _ _ c w2 hlk2]
  simp only [putNode, writerWP_modify]
  have htk2 : w2.taken.contains (X (D + 1)) = false := by rw [h2t, h1t]; exact htk
  have key : ∀ w3 : W, w3.nodes = upsert w2.nodes (X (D + 1)) ((Nn (D + 1)).toPrev (c.i - 1)) →
      w3.taken = w2.taken → w3.top = w2.top →
      LiveEdges c.p (wNode c.p base w3) c.i w3.top.rootKey ∧
        (∀ z, TReach (wNode c.p base w3) c.i w3.top.rootKey z →
          (TReach (updN (wNode c.p base w) (X (D + 1)) ⟨(Nn (D + 1)).leaf, last.ks⟩) c.i w.top.rootKey z ∨ w.next ≤ z) ∧ z ≠ X (D + 1)) ∧
        w3.taken = w.taken := by
    intro w3 h3n h3t h3top
    have hN3 := wNode_upsert_updN c.p base w2 w3 (X (D + 1)) _ h3n h3t htk2
    have hxR2 : ¬ TReach (wNode c.p base w2) c.i w2.top.rootKey (X (D + 1)) := by
      intro h
      rcases h2reach _ h with h' | h'
      · rw [h1top] at h'
        exact (hR1V _ h').2 rfl
      · have := hXlt (D + 1) (Nat.le_refl _); rw [h1next] at h'; omega
    have hLV' := (liveEdgesX_false_iff _ _ _ _).mp hLV
    rw [← h1top] at hLV'
    refine ⟨?_, ?_, by rw [h3t, h2t, h1t]⟩
    · rw [hN3, h3top]
      exact liveEdges_updN_unreach _ _ _ _ _ _ hxR2 (h2live hmp hLV')
    · intro z hz
      rw [hN3, h3top] at hz
      have hz2 := tReach_updN_unreach _ c.i _ _ _ hxR2 z hz
      rcases h2reach z hz2 with h' | h'
      · rw [h1top] at h'
        obtain ⟨h1, h2⟩ := hR1V z h'
        exact ⟨h1.imp id (fun h => by omega), h2⟩
      · rw [h1next] at h'
        have := hXlt (D + 1) (Nat.le_refl _)
        exact ⟨Or.inr (by omega), by omega⟩
  exact key _ rfl rfl rfl


/-- The instance of `SplitStepOKX` for p below q (depth d' + 1), not made by the
transaction, split in time (it compacts, or its last version is within the split's
bound), whatever q's room: the time split and its cascade on the merged tree
(`writerWP_handleFull_timeChainV_live`), with the path's facts at the merge's
start w3 and w3's tree. -/
theorem splitStepOKX_timeChain (c : Ctx) (base : View BVal) (hmp : MergeParamsOK c.p) (d' : Nat)
    (p : NodeId) (pn : KNode) (Lst : KNode → Prop) (C : Prop) (w3 : W) (x : NodeId)
    (X : Nat → NodeId) (K : Nat → Nat) (Nn : Nat → KNode)
    (hP : PathOK c w3 (d' + 1) X K Nn) (hXp : X (d' + 1) = p) (hNp : Nn (d' + 1) = pn)
    (hpnew : pn.firstTime ≠ some c.i) (htime : ∀ last, Lst last → C ∨ last.size ≤ c.p.splitAbove)
    (hxX : ∀ i, i ≤ d' + 1 → X i ≠ x) (hXlt : ∀ i, i ≤ d' + 1 → X i < w3.next)
    (hT3 : TreeOK (wNode c.p base w3) c.i w3.top.rootKey)
    (hRO : RangeOrder (wNode c.p base w3) c.i w3.top.rootKey)
    (hwf : ∀ y yn, wNode c.p base w3 y = some yn → klongsWf yn.ks = true)
    (htm : ∀ y yn, wNode c.p base w3 y = some yn → ∀ s, Klong.time s ∈ yn.ks → s ≤ c.i)
    (hG3 : ∀ u un c' z, wNode c.p base w3 u = some un → (c', z) ∈ un.liveAt c.i → z < w3.next)
    (hfr3 : ∀ z, w3.next ≤ z → knodeOf c.p base z = none) :
    SplitStepOKX c base (d' + 1) p pn Lst C w3 x := by
  intro w last compact pairs _ _ hLst hcomp _ _ _ hTV hfree hlinksV hLE hpath hlook htk hnext htop hTw
    hRw hnone hlinkw _
  obtain ⟨hX, hK, hS2, hlinkK, h0⟩ := id hP
  subst hXp hNp
  have hcs : (!compact && decide (last.size > c.p.splitAbove)) = false := by
    rcases htime last hLst with hC | hle
    · rw [hcomp.mpr hC]; rfl
    · have : ¬ (last.size > c.p.splitAbove) := by omega
      simp [this]
  have hwX : ∀ i, i ≤ d' + 1 → wNode c.p base w3 (X i) = some (Nn i) := by
    intro i hi
    obtain ⟨a, b⟩ := hS2 i hi
    simp only [wNode, b, Bool.false_eq_true, ↓reduceIte, a]
  have hreach3 := pathOK_reach c base w3 (d' + 1) X K Nn hP
  have hdist := pathOK_dist c base w3 (d' + 1) X K Nn hP hT3
  have hsa2 : 2 ≤ c.p.splitAbove := by have := hmp.1; have := hmp.2.2.1; omega
  unfold handleFull
  show WriterWP (handleFullWith (fun q more => appendKlongs d' q more) (d' + 1) (X (d' + 1)) [] last
    compact) c w _
  exact writerWP_handleFull_timeChainV_live c base w3.path d' X K Nn last compact hX hK hlinkK
    (fun i h1 hi hNR hql' c' z hz hpos =>
      rangeG_of_rangeOrder c _ _ hRO htm _ _ _ _ _ (hreach3 (i - 1) (by omega)) (hwX (i - 1) (by omega))
        hql' (hlinkK i h1 (by omega)) (hwX i (by omega)) hNR c' z hz hpos)
    (fun i _ hi hNR hsp' => lenG_of_splitAbove c _ _ hsa2 _ _ (hreach3 i (by omega)) (hwX i (by omega))
      hNR hsp')
    (fun i hi => hwf _ _ (hwX i hi)) (fun i hi => htm _ _ (hwX i hi)) hdist hpnew hcs hmp w hpath
    (fun i hi => ⟨by rw [hlook _ (hxX i hi) (hXlt i hi)]; exact (hS2 i hi).1,
      by rw [htk]; exact (hS2 i hi).2⟩)
    hTw (fun i hi => hRw _ (hreach3 i hi))
    (fun z hz => ⟨hnone z hz, (hfree z hz).2, hfr3 z (by omega)⟩)
    (fun u c' z hl => by
      rcases hlinkw u c' z hl with ⟨un, hun, hc⟩ | h
      · have := hG3 u un c' z hun hc; omega
      · omega)
    (by rw [htop]; exact h0.symm) hTV hlinksV hLE

/-- The merge's full parent p, not made by the transaction, split in time below q
(d ≥ 2), whatever q's room (the cascade), with no hole after: a merge into two
nodes, or into one whose last version holds m live klongs or more. -/
def MergeFullTimeChain (c : Ctx) (v3 : W) (d : Nat) (p : NodeId) (pn xn ln rn : KNode)
    (il cL ir cR : Nat) : Prop :=
  pn.firstTime ≠ some c.i ∧ 2 ≤ d ∧
  (∀ last, mergeFullLast pn c.i cL v3.next cR (mergeM2 c xn ln rn cR v3.next) = some last →
    pn.size + mergeParentNeed c.i pn il ir cR (mergeM2 c xn ln rn cR v3.next) ≤ c.p.M ∨
      last.size ≤ c.p.splitAbove) ∧
  (mergeM2 c xn ln rn cR v3.next = none → ∀ last,
    mergeFullLast pn c.i cL v3.next cR none = some last →
      c.p.mergeBelow ≤ ((⟨pn.leaf, last.ks⟩ : KNode).liveAt c.i).length)

set_option maxHeartbeats 4000000 in
/-- The case `MergeFullTimeChain` at a round with `MergeLiveOK`'s facts: the merge's
tail ends with the live counts, no hole. -/
theorem writerWP_mergeTail_liveTimeChainRound (c : Ctx) (base : View BVal)
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
    (hN : MergeFullTimeChain c v3 d p pn xn ln rn il cL ir cR) :
    WriterWP (mergeTail c x d p pn xn leftSome l ln il r rn ir) c w3
      (fun res v4 => (res = 1 → LiveHoleW key g (h + 1) c base v4) ∧
        (res ≠ 1 → LiveEdges c.p (wNode c.p base v4) c.i v4.top.rootKey)) := by
  obtain ⟨hpnew, hd2, htime, hfill⟩ := hN
  refine writerWP_mergeTail_liveSplitRoundX c base hvc hm hMP key g h v v1 v3 d F w0 k0 KO X K Nn x p
    pn xn hS hd hr13 hk13 hp13 hLH hJ3 hP3 hx hpath hplk hpleaf hxlk leftSome l ln il r rn ir cL cR w3
    hr3 h3p hsrc3 hL hLL hR hRL hclt hadj hll hrl hxlr hln hrn hpre3 hpath3 hnB ?_
    (fun hm2 last hl => Or.inr (hfill hm2 last hl))
  have hI : PutInv c base v3 := hJ3.1.1.1
  have hG : PutInvG c base v3 := hJ3.1.1.2.1
  have hRO : RangeOrder (wNode c.p base v3) c.i v3.top.rootKey := hJ3.1.1.2.2.1
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 2 := ⟨d - 2, by omega⟩
  have hd1' : d' + 2 - 1 = d' + 1 := by omega
  rw [hd1'] at hpath ⊢
  obtain ⟨hX, hK, hS2, hlinkK, h0⟩ := id hP3
  have hXi : ∀ i, i ≤ d' + 2 → ∀ z, (v3.path[i]?).map (·.2) = some z → z = X i := by
    intro i hi z hz; have := hX i hi; rw [hz] at this; exact Option.some.inj this
  have hpX := hXi (d' + 1) (by omega) p hpath
  have hxX := hXi (d' + 2) (Nat.le_refl _) x hx
  have hpnN : Nn (d' + 1) = pn := by
    have := (hS2 (d' + 1) (by omega)).1; rw [← hpX, hplk] at this; exact (Option.some.inj this).symm
  have hdist := pathOK_dist c base v3 (d' + 2) X K Nn hP3 hI.tree
  have hN3 : wNode c.p base w3 = wNode c.p base v3 := hr3.1
  have hnx : w3.next = v3.next := hr3.2.2.2.2
  refine splitStepOKX_timeChain c base hMP d' p pn _ _ w3 x X K Nn
    ⟨fun i hi => by rw [hpath3]; exact hX i (by omega),
      fun i h1 hi => by rw [hpath3]; exact hK i h1 (by omega),
      fun i hi => ⟨lookup_of_prefix _ _ hpre3 _ _ (hS2 i (by omega)).1,
        by rw [hr3.2.2.1]; exact (hS2 i (by omega)).2⟩,
      fun i h1 hi => hlinkK i h1 (by omega), by rw [h0, hr3.2.1]⟩
    hpX.symm hpnN hpnew htime
    (fun i hi he => by rw [hxX] at he; have := hdist i (d' + 2) (by omega) (Nat.le_refl _) he; omega)
    (fun i hi => by
      rw [hnx]; exact hI.ids.1 (X i) (by rw [(hS2 i (by omega)).1]; rfl))
    (by rw [hN3, hr3.2.1]; exact hI.tree) (by rw [hN3, hr3.2.1]; exact hRO)
    (by rw [hN3]; exact hI.wf) (by rw [hN3]; exact hI.times)
    (by rw [hN3, hnx]; exact hG.links)
    (fun z hz => (hI.fresh z (by rw [← hnx]; exact hz)).1)

/-! ## What is left of `MergeTailFullRest8OK` -/

/-- `MergeTailFullRest8OK` but in its case `MergeFullTimeChain` (bergdb 030-01, step
3's rest): the merge's tail where its parent p goes `full`, and p, not made by the
transaction, splits in time below q with a merge into one node that leaves p's last
version with fewer than m live klongs (the hole, below the cascade or q split in
space), or in space below a full inner parent; or p, made by the transaction, splits
in space (in place). -/
def MergeTailFullRest9OK (c : Ctx) (base : View BVal) (B : NodeId) (H : NodeId → Nat → Prop) :
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
    ¬ MergeFullTimeRoomG c v3 d p pn xn ln rn il cL ir cR →
    ¬ MergeFullSpaceG c v3 d p pn xn ln rn il cL ir cR →
    ¬ MergeFullTimeRoot1 c v3 d pn xn ln rn il cL ir cR →
    ¬ MergeFullSpaceSegChain c v3 d p pn xn ln rn il cL ir cR →
    ¬ MergeFullRootX c v3 d p pn xn ln rn il cL ir cR →
    ¬ MergeFullTimeChain c v3 d p pn xn ln rn il cL ir cR →
    WriterWP (mergeTail c x d p pn xn leftSome l ln il r rn ir) c w3
      (fun res v4 => (res = 1 → LiveHoleW key g (h + 1) c base v4) ∧
        (res ≠ 1 → LiveEdges c.p (wNode c.p base v4) c.i v4.top.rootKey))

/-- `MergeTailFullRest8OK` from its rest: its case `MergeFullTimeChain` (a time split
below q, the cascade included, with no hole after) is proved
(`writerWP_mergeTail_liveTimeChainRound`). -/
theorem mergeTailFullRest8OK_of_rest9 (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (hm : c.p.merges = true) (hMP : MergeParamsOK c.p) {B : NodeId} {H : NodeId → Nat → Prop}
    (hF : MergeTailFullRest9OK c base B H) :
    MergeTailFullRest8OK c base B H := by
  intro key g h v v1 v3 d F w0 k0 KO top0 X K Nn x p pn xn hS hd hr13 hk13 hp13 hLH hJ3 hpb3 hP3 hb1
    hi1 hpf1 hi3 hx hpath hplk hpleaf hxlk hcnt leftSome l ln il r rn ir cL cR w3 hr3 h3p hk3 hsrc3
    hL hLL hR hRL hclt hadj hll hrl hxlr hln hrn hpre3 hpath3 hnB hNT hNM hNS hNG hNSG hNR hNC hNX
  by_cases hN : MergeFullTimeChain c v3 d p pn xn ln rn il cL ir cR
  · exact writerWP_mergeTail_liveTimeChainRound c base hvc hm hMP key g h v v1 v3 d F w0 k0 KO X K Nn
      x p pn xn hS hd hr13 hk13 hp13 hLH hJ3 hP3 hx hpath hplk hpleaf hxlk leftSome l ln il r rn ir cL
      cR w3 hr3 h3p hsrc3 hL hLL hR hRL hclt hadj hll hrl hxlr hln hrn hpre3 hpath3 hnB hN
  · exact hF key g h v v1 v3 d F w0 k0 KO top0 X K Nn x p pn xn hS hd hr13 hk13 hp13 hLH hJ3 hpb3 hP3
      hb1 hi1 hpf1 hi3 hx hpath hplk hpleaf hxlk hcnt leftSome l ln il r rn ir cL cR w3 hr3 h3p hk3
      hsrc3 hL hLL hR hRL hclt hadj hll hrl hxlr hln hrn hpre3 hpath3 hnB hNT hNM hNS hNG hNSG hNR hNC hNX
      hN

/-- `afterDelete` with the hole (bergdb 030-01, steps 3 and 4): from the call's
facts to `LiveEdges`, premises `MergeTailFullRest9OK`, `MergeParamsOK` and R3
after the merges' loop. -/
theorem writerWP_afterDelete_liveTR9 (key : Key) (g : Nat) (c : Ctx) (base : View BVal)
    (hvc : ViewCoherent c base) (hm : c.p.merges = true) (hMP : MergeParamsOK c.p) (KO : KindOracle)
    (B : NodeId) (hv : ViewIdsBelow B c.view) (hk : ViewKinds KO B c)
    (hICEk : ICEFromKinds c base KO B) (hsa2 : 2 ≤ c.p.splitAbove) (hcap : 1 ≤ c.p.mergeMax)
    (hpos : 0 < c.i) {H : NodeId → Nat → Prop} (hvo : ViewHtOK H B c)
    (hkw : ViewKlongsWf c.p c.view) (top0 : Top) (hB : PutBase c base B)
    (hF : MergeTailFullRest9OK c base B H)
    (v : W) (hJ : DelInvJAE c base KO B B v) (hpb : PutBook c B top0 v) (hhi : HtInv H B c v)
    (hLH : LiveHoleW key g 0 c base v)
    (hR3 : WriterWP (mergeUp key g c.p.fuel 0 false) c v
      (fun merged v' => merged = true → R3At key g c v')) :
    WriterWP (afterDelete key g 0) c v
      (fun _ v' => LiveEdges c.p (wNode c.p base v') c.i v'.top.rootKey) :=
  writerWP_afterDelete_liveTR8 key g c base hvc hm hMP KO B hv hk hICEk hsa2 hcap hpos hvo hkw top0 hB
    (mergeTailFullRest8OK_of_rest9 c base hvc hm hMP hF) v hJ hpb hhi hLH hR3

end SIS.Tree
