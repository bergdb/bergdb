/-
A full node's split with a last version given by the caller, and its cascade
(bergdb 024-22): `writerWP_delSplit_chainG` for any last version whose tree is a
tree, for the merge's full parent (`mergeParent`'s `full`).
-/
import SIS.Tree.WriterTreeDelChain

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- `writerWP_delSplit_chainG` for any last version `last` (a delete's, or a
merge's parent with its new pointers): given that the tree with X (D + 1)'s node
replaced by `last` is a tree (`hVt`) and `last` names nodes below the next id
(`hvx`), the split and its cascade keep the tree, every node reached after
reached in that tree or new. The node X (D + 1) splits in time or in space (by
`last`'s size and `compact`), in place if the transaction made it, below an
inner node or a segment leaf; then the
cascade above it (`writerWP_appendKlongs_chainG`, its premises for X s .. X D).
The halves of `last` (`hhalves`): the divider r, the first half's links below
it, the second half's from it, and r in the range of an inner parent's link.
From a state whose tree is a tree, the writer's tree after the split is a tree;
the top is kept unless the space root split; nodes below the next id but the
path's are kept; every node reached was reached before or is new. -/
theorem writerWP_fullSplit_chainG (c : Ctx) (base : View BVal)
    (path0 : List (Option Nat × NodeId)) (s D : Nat) (X : Nat → NodeId) (K : Nat → Nat)
    (Nn : Nat → KNode) (last : KNode) (compact : Bool) (hsD : s ≤ D)
    (hX : ∀ i, s ≤ i → i ≤ D + 1 → (path0[i]?).map (·.2) = some (X i))
    (hK : ∀ i, s < i → i ≤ D + 1 → path0[i]? = some (some (K i), X i))
    (hlinkK : ∀ i, s < i → i ≤ D + 1 → (K i, X i) ∈ (Nn (i - 1)).liveAt c.i)
    (hrange : ∀ i, s < i → i ≤ D → ¬ ChainRoom c (Nn i) → (Nn (i - 1)).leaf = false →
      ∀ c' z, (c', z) ∈ (Nn i).live → 0 < c' →
      K i ≤ c' ∧ ∀ c'' z', (c'', z') ∈ (Nn (i - 1)).live → K i < c'' → c' < c'')
    (hlen : ∀ i, s ≤ i → i ≤ D → ¬ ChainRoom c (Nn i) →
      c.p.splitAbove < ((Nn i).lastVersion c.i).size →
      2 ≤ (Nn i).live.length)
    (hwf : ∀ i, s ≤ i → i ≤ D + 1 → klongsWf (Nn i).ks = true)
    (htimes : ∀ i, s ≤ i → i ≤ D + 1 → ∀ t, Klong.time t ∈ (Nn i).ks → t ≤ c.i)
    (htop : ChainRoom c (Nn s) ∨ s = 0)
    (hdist : ∀ i i', s ≤ i → i ≤ D + 1 → s ≤ i' → i' ≤ D + 1 → X i = X i' → i = i')
    (hhalves : c.p.splitAbove < last.size → ∃ r : Nat, 0 < r ∧
      (halves (Nn (D + 1)).leaf c.i last []).2.2 = r ∧
      (∀ c' z, (c', z) ∈ (halves (Nn (D + 1)).leaf c.i last []).1.liveAt c.i → c' < r ∧
        (c', z) ∈ (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode).liveAt c.i) ∧
      (∀ c' z, (c', z) ∈ (halves (Nn (D + 1)).leaf c.i last []).2.1.liveAt c.i → ∃ c0, r ≤ c0 ∧
        c' = splitLocalCv (Nn (D + 1)).leaf r c0 ∧
        (c0, z) ∈ (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode).liveAt c.i) ∧
      ((Nn D).leaf = false →
        K (D + 1) ≤ r ∧ ∀ c'' z', (c'', z') ∈ (Nn D).live → K (D + 1) < c'' → r < c''))
    (w : W) (hS1 : w.path = path0)
    (hS2 : ∀ i, s ≤ i → i ≤ D + 1 →
      w.nodes.lookup (X i) = some (Nn i) ∧ w.taken.contains (X i) = false)
    (hS3 : TreeOK (wNode c.p base w) c.i w.top.rootKey)
    (hS4 : ∀ i, s ≤ i → i ≤ D + 1 → TReach (wNode c.p base w) c.i w.top.rootKey (X i))
    (hS5 : ∀ z, w.next ≤ z → w.nodes.lookup z = none ∧ w.taken.contains z = false ∧
      knodeOf c.p base z = none)
    (hS6 : ∀ u c' z, TLink (wNode c.p base w) c.i u c' z → z < w.next)
    (hR0 : s = 0 → w.top.rootKey = X 0)
    (hVt : TreeOK (updN (wNode c.p base w) (X (D + 1)) (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode)) c.i
      w.top.rootKey)
    (hvx : ∀ c' z, (c', z) ∈ (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode).liveAt c.i → z < w.next) :
    WriterWP (handleFullWith (fun q more => appendKlongs D q more) (D + 1) (X (D + 1)) [] last
      compact) c w (fun _ w' =>
      TreeOK (wNode c.p base w') c.i w'.top.rootKey ∧
      ((w'.top = w.top ∨ (s = 0 ∧ w.next ≤ w'.top.rootKey)) ∧ w'.taken = w.taken ∧
        w'.path = w.path ∧ w.next ≤ w'.next ∧ w'.vals = w.vals) ∧
      (∀ z, z < w.next → (∀ i, s ≤ i → i ≤ D + 1 → z ≠ X i) →
        w'.nodes.lookup z = w.nodes.lookup z) ∧
      (∀ z, TReach (wNode c.p base w') c.i w'.top.rootKey z →
        TReach (updN (wNode c.p base w) (X (D + 1)) (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode)) c.i w.top.rootKey z ∨ w.next ≤ z)) := by
  have hchain := writerWP_appendKlongs_chainG c base path0 s D X K Nn
    (fun i h1 h2 => hX i h1 (by omega)) (fun i h1 h2 => hK i h1 (by omega))
    (fun i h1 h2 => hlinkK i h1 (by omega)) hrange hlen
    (fun i h1 h2 => hwf i h1 (by omega)) (fun i h1 h2 => htimes i h1 (by omega)) htop
    (fun i i' h1 h2 h3 h4 => hdist i i' h1 (by omega) h3 (by omega)) (D - s) (by omega)
  have hsD' : s + (D - s) = D := by omega
  rw [hsD'] at hchain
  have hj : s < D + 1 := by omega
  obtain ⟨hlk, htk⟩ := hS2 (D + 1) (by omega) (Nat.le_refl _)
  obtain ⟨hlq, htq⟩ := hS2 D hsD (by omega)
  have hV := hVt
  have hRV : ∀ z, TReach (updN (wNode c.p base w) (X (D + 1)) (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode)) c.i
      w.top.rootKey z → TReach (updN (wNode c.p base w) (X (D + 1)) (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode)) c.i
      w.top.rootKey z := fun _ h => h
  have hpq : (w.path[D]?).map (·.2) = some (X (D)) := by
    rw [hS1]; exact hX (D) (by omega) (by omega)
  have hpk : w.path[D + 1]? = some (some (K (D + 1)), X (D + 1)) := by
    rw [hS1]; exact hK (D + 1) hj (Nat.le_refl _)
  have hkl : (K (D + 1), X (D + 1)) ∈ (Nn (D)).liveAt c.i := by
    have := hlinkK (D + 1) hj (Nat.le_refl _); simpa using this
  obtain ⟨hfree0, htk0, hbase0⟩ := hS5 w.next (Nat.le_refl _)
  obtain ⟨hfree2, htk2', hbase2⟩ := hS5 (w.next + 2) (by omega)
  have hwnext : wNode c.p base w w.next = none := by
    simp only [wNode, htk0, Bool.false_eq_true, ↓reduceIte, hfree0, hbase0]
  have hwnext2 : wNode c.p base w (w.next + 2) = none := by
    simp only [wNode, htk2', Bool.false_eq_true, ↓reduceIte, hfree2, hbase2]
  have hnoLink : ∀ z, w.next ≤ z → ∀ u c', ¬ TLink (wNode c.p base w) c.i u c' z := by
    intro z hz u c' hl; have := hS6 u c' z hl; omega
  have hyR : ∀ z, w.next ≤ z → ¬ TReach (wNode c.p base w) c.i w.top.rootKey z := by
    intro z hz
    have hwz : wNode c.p base w z = none := by
      obtain ⟨a, b, d⟩ := hS5 z hz
      simp only [wNode, b, Bool.false_eq_true, ↓reduceIte, a, d]
    exact not_reach_fresh _ c.i _ z hS3 hwz (fun u c' _ => hnoLink z hz u c')
  have hXlt : ∀ i, s ≤ i → i ≤ D + 1 → X i < w.next := by
    intro i h1 h2
    obtain ⟨hl, _⟩ := hS2 i h1 h2
    rcases Nat.lt_or_ge (X i) w.next with hlt | hge
    · exact hlt
    · have := (hS5 (X i) hge).1
      rw [hl] at this; cases this
  have hqx : X (D) ≠ X (D + 1) := by
    intro h; have := hdist _ _ (by omega) (by omega) (by omega) (Nat.le_refl _) h; omega
  have hwq : wNode c.p base w (X (D)) = some (Nn (D)) := by
    simp only [wNode, htq, Bool.false_eq_true, ↓reduceIte, hlq]
  have hwx : wNode c.p base w (X (D + 1)) = some (Nn (D + 1)) := by
    simp only [wNode, htk, Bool.false_eq_true, ↓reduceIte, hlk]
  have hqR : TReach (updN (wNode c.p base w) (X (D + 1))
      (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode)) c.i w.top.rootKey
      (X (D)) :=
    tReach_updN_parent _ c.i _ _ _ _ _ hS3 (hS4 (D) (by omega) (by omega))
      ⟨Nn (D), hwq, hkl⟩
  have hqtimes := htimes (D) (by omega) (by omega)
  have hqwf := hwf (D) (by omega) (by omega)
  have hxtimes := htimes (D + 1) (by omega) (Nat.le_refl _)
  have hxwf := hwf (D + 1) (by omega) (Nat.le_refl _)
  -- the links of the node with the klongs put are below the next id
  have hvxLinks : ∀ c' z, (c', z) ∈ (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode).liveAt c.i → z < w.next := by
    intro c' z h
    exact hvx c' z h
  have hVfresh : ∀ z, w.next ≤ z → ∀ u c', TReach (updN (wNode c.p base w) (X (D + 1))
      (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode)) c.i w.top.rootKey u →
      ¬ TLink (updN (wNode c.p base w) (X (D + 1))
        (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode)) c.i u c' z := by
    intro z hz u c' _ hl
    obtain ⟨m, hm, hc⟩ := hl
    by_cases hu : u = X (D + 1)
    · rw [hu, updN_self] at hm
      simp only [Option.some.injEq] at hm
      subst hm
      have := hvxLinks c' z hc; omega
    · rw [updN_ne _ _ _ _ hu] at hm
      exact hnoLink z hz u c' ⟨m, hm, hc⟩
  -- the rest of a split: the parent's step by the induction, then the node left behind
  have hfinish : ∀ (w1 : W) (ins' : List (Nat × NodeId)) (N1 : NodeId → Option KNode)
      (New : NodeId → Prop),
      InsOK (Nn (D)) ins' → (∀ q ∈ ins', q.2 < w1.next) →
      w1.path = w.path → w1.taken = w.taken → w1.top = w.top → w.next + 2 ≤ w1.next →
      w1.vals = w.vals → (∀ z, New z → w.next ≤ z) →
      (∀ z, z < w.next → w1.nodes.lookup z = w.nodes.lookup z) →
      wNode c.p base w1 = N1 →
      TreeOK N1 c.i w.top.rootKey →
      (∀ i, s ≤ i → i ≤ D → TReach N1 c.i w.top.rootKey (X i)) →
      (∀ z, w1.next ≤ z → w1.nodes.lookup z = none ∧ w1.taken.contains z = false ∧
        knodeOf c.p base z = none) →
      (∀ u c' z, TLink N1 c.i u c' z → z < w1.next) →
      TreeOK (updN N1 (X (D)) (ins'.foldl (fun n (cv, y) => n.add c.i (.key cv y))
        (Nn (D)))) c.i w.top.rootKey →
      (∀ z, TReach (updN N1 (X (D)) (ins'.foldl (fun n (cv, y) => n.add c.i (.key cv y))
        (Nn (D)))) c.i w.top.rootKey z →
        (TReach (updN (wNode c.p base w) (X (D + 1))
          (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode)) c.i
          w.top.rootKey z ∨ New z) ∧ z ≠ X (D + 1)) →
      WriterWP (appendKlongs (D) (X (D)) ins') c w1 (fun _ w2 =>
        WriterWP (do let m ← getNode (X (D + 1)); putNode (X (D + 1)) (m.toPrev (c.i - 1)))
          c w2 (fun _ w3 =>
          TreeOK (wNode c.p base w3) c.i w3.top.rootKey ∧
          ((w3.top = w.top ∨ (s = 0 ∧ w.next ≤ w3.top.rootKey)) ∧ w3.taken = w.taken ∧ w3.path = w.path ∧ w.next ≤ w3.next ∧ w3.vals = w.vals) ∧
          (∀ z, z < w.next → (∀ i, s ≤ i → i ≤ D + 1 → z ≠ X i) →
            w3.nodes.lookup z = w.nodes.lookup z) ∧
          (∀ z, TReach (wNode c.p base w3) c.i w3.top.rootKey z →
            TReach (updN (wNode c.p base w) (X (D + 1)) (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode)) c.i w.top.rootKey z ∨ w.next ≤ z))) := by
    intro w1 ins' N1 New hins' hinsT' h1path h1t h1top h1next h1vals hNew h1low hN1 hT1 hR1 hS5' hS6' hV1 hRV1
    have hpar := hchain w1 ins' hins' hinsT' (by rw [h1path, hS1])
      (by
        intro i h1 h2
        obtain ⟨a, b⟩ := hS2 i h1 (by omega)
        refine ⟨?_, by rw [h1t]; exact b⟩
        rw [h1low _ (hXlt i h1 (by omega)), a])
      (by rw [hN1, h1top]; exact hT1)
      (by intro i h1 h2; rw [hN1, h1top]; exact hR1 i h1 h2)
      hS5' (by rw [hN1]; exact hS6') (fun h0 => by rw [h1top]; exact hR0 h0)
      (by rw [hN1, h1top]; exact hV1)
    refine writerWP_mono hpar ?_
    rintro _ w2 ⟨hT2, ⟨h2top, h2t, h2path, h2next, h2vals⟩, h2frame, h2reach⟩
    have hlk2 : w2.nodes.lookup (X (D + 1)) = some (Nn (D + 1)) := by
      rw [h2frame _ (by have := hXlt (D + 1) (by omega) (Nat.le_refl _); omega)
        (fun i h1 h2 he => by have := hdist _ _ (by omega) (Nat.le_refl _) h1 (by omega) he; omega),
        h1low _ (hXlt (D + 1) (by omega) (Nat.le_refl _)), hlk]
    simp only [writerWP_bind]
    rw [writerWP_getNode_known _ _ c w2 hlk2]
    simp only [putNode, writerWP_modify]
    have htk2 : w2.taken.contains (X (D + 1)) = false := by rw [h2t, h1t]; exact htk
    generalize hw3 : ({ w2 with nodes := upsert w2.nodes (X (D + 1)) ((Nn (D + 1)).toPrev (c.i - 1)) } : W) = w3
    have h3n : w3.nodes = upsert w2.nodes (X (D + 1)) ((Nn (D + 1)).toPrev (c.i - 1)) := by
      rw [← hw3]
    have h3t : w3.taken = w2.taken := by rw [← hw3]
    have hN3 := wNode_upsert_updN c.p base w2 w3 (X (D + 1)) _ h3n h3t htk2
    have hxR2 : ¬ TReach (wNode c.p base w2) c.i w2.top.rootKey (X (D + 1)) := by
      intro h
      rcases h2reach _ h with h' | h'
      · rw [hN1, h1top] at h'
        exact (hRV1 _ h').2 rfl
      · have := hXlt (D + 1) (by omega) (Nat.le_refl _); omega
    refine ⟨?_, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
    · rw [hN3]; exact treeOK_updN_unreach _ c.i _ _ _ hT2 hxR2
    · rcases h2top with h | ⟨h0, h⟩
      · exact Or.inl (h.trans h1top)
      · exact Or.inr ⟨h0, by omega⟩
    · rw [h2t, h1t]
    · rw [h2path, h1path]
    · omega
    · rw [h2vals, h1vals]
    · intro z hz hzX
      rw [lookup_upsert, ite_eq_right_of_eq_false _ _ (eq_false (hzX _ (by omega) (Nat.le_refl _))),
        h2frame z (by omega) (fun i h1 h2 => hzX i h1 (by omega)), h1low z hz]
    · intro z hz
      rw [hN3] at hz
      have hz2 := tReach_updN_unreach _ c.i _ _ _ hxR2 z hz
      rcases h2reach z hz2 with h' | h'
      · rw [hN1, h1top] at h'
        rcases (hRV1 z h').1 with h'' | h''
        · exact Or.inl (hRV z h'')
        · exact Or.inr (hNew z h'')
      · exact Or.inr (by omega)
  have hanc : ∀ m : KNode, ∀ i, s ≤ i → i ≤ D →
      TReach (updN (wNode c.p base w) (X (D + 1)) m) c.i w.top.rootKey (X i) :=
    fun m i h1 h2 => chain_anc_reach (wNode c.p base w) c.i w.top.rootKey X s (D + 1) hS3
      (hS4 s (Nat.le_refl _) (by omega))
      (fun i' h1' h2' => by
        obtain ⟨a, b⟩ := hS2 (i' - 1) (by omega) (by omega)
        exact ⟨K i', Nn (i' - 1), by simp only [wNode, b, Bool.false_eq_true, ↓reduceIte, a],
          hlinkK i' h1' (by omega)⟩) m i h1 (by omega)
  -- a time split, for either flag
  have hstepT : (Nn (D + 1)).firstTime ≠ some c.i → ∀ compact : Bool,
      (!compact && decide (last.size > c.p.splitAbove)) = false →
      WriterWP (handleFullWith (fun q more => appendKlongs (D) q more) (D + 1)
        (X (D + 1)) [] last compact) c w (fun _ w' =>
        TreeOK (wNode c.p base w') c.i w'.top.rootKey ∧
        ((w'.top = w.top ∨ (s = 0 ∧ w.next ≤ w'.top.rootKey)) ∧ w'.taken = w.taken ∧ w'.path = w.path ∧ w.next ≤ w'.next ∧ w'.vals = w.vals) ∧
        (∀ z, z < w.next → (∀ i, s ≤ i → i ≤ D + 1 → z ≠ X i) →
          w'.nodes.lookup z = w.nodes.lookup z) ∧
        (∀ z, TReach (wNode c.p base w') c.i w'.top.rootKey z →
          TReach (updN (wNode c.p base w) (X (D + 1)) (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode)) c.i w.top.rootKey z ∨ w.next ≤ z)) := by
    intro hfirst compact hcs
    apply writerWP_handleFullWith_time_up_last' (D) (X (D + 1)) (X (D)) (Nn (D + 1))
      (Nn (D)) (K (D + 1)) last compact c w hlk hlq hfirst hcs hpq hpk
    intro w1 h1n h1t h1top h1path h1next h1vals
    have hN1 : wNode c.p base w1 = updN (wNode c.p base w) w.next ⟨(Nn (D + 1)).leaf, last.ks⟩ :=
      wNode_append_updN c.p base w w1 _ h1n h1t hfree0 htk0
    have hlsub : ∀ c' z, (c', z) ∈ (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode).liveAt c.i →
        (c', z) ∈ (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode).liveAt c.i := fun _ _ h => h
    obtain ⟨hT1V, hR1V⟩ := treeOK_timeSplit_gen (updN (wNode c.p base w) (X (D + 1))
        (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode))
      (updN (wNode c.p base w1) (X (D)) ([(K (D + 1), w.next)].foldl
        (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (D)))) c.i w.top.rootKey (X (D))
      (X (D + 1)) w.next (Nn (D))
      (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode)
      ⟨(Nn (D + 1)).leaf, last.ks⟩
      ([(K (D + 1), w.next)].foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (D)))
      (K (D + 1)) hV hqR (by rw [updN_ne _ _ _ _ hqx]; exact hwq)
      hkl (updN_self _ _ _) (updN_self _ _ _)
      (fun c' z h => KNode.add_key_liveAt_mem _ c.i _ _ hqwf hqtimes c' z h)
      (by
        rw [updN_ne _ _ _ _ (fun h => by have := hXlt (D) (by omega) (by omega); omega), hN1]
        exact updN_self _ _ _)
      hlsub
      (by
        intro z hz1 hz2 hz3
        rw [updN_ne _ _ _ _ hz2, hN1, updN_ne _ _ _ _ hz3]
        exact (updN_ne _ _ _ _ hz1).symm)
      (by
        rw [updN_ne _ _ _ _ (fun h => by
          have := hXlt (D + 1) (by omega) (Nat.le_refl _); omega)]
        exact hwnext)
      (hVfresh w.next (Nat.le_refl _))
    apply hfinish w1 [(K (D + 1), w.next)] _ (fun z => z = w.next)
      (Or.inl ⟨_, _, rfl⟩) (by intro q hq; simp at hq; rw [hq, h1next]; simp)
      h1path h1t h1top (by omega) h1vals (fun z hz => by have h : z = w.next := hz; omega)
      (by
        intro z hz
        rw [h1n, List.lookup_append]
        cases h : w.nodes.lookup z with
        | some _ => rfl
        | none =>
          have hb : (z == w.next) = false := by simp only [beq_eq_false_iff_ne, ne_eq]; omega
          simp [List.lookup, hb])
      hN1
      (treeOK_updN_unreach _ c.i _ _ _ hS3 (hyR w.next (Nat.le_refl _)))
      (by
        intro i h1 h2
        obtain ⟨a, ha⟩ := (hS4 i h1 (by omega)).pathLen
        exact tReach_updN_of_short _ c.i _ _ _ a _ ha
          (fun b hb => absurd hb.reach (hyR w.next (Nat.le_refl _))))
      (by
        intro z hz
        rw [h1next] at hz
        obtain ⟨a, b, d⟩ := hS5 z (by omega)
        refine ⟨?_, by rw [h1t]; exact b, d⟩
        rw [h1n, List.lookup_append, a]
        have hb : (z == w.next) = false := by simp only [beq_eq_false_iff_ne, ne_eq]; omega
        simp [List.lookup, hb])
      (by
        intro u c' z hl
        rw [h1next]
        obtain ⟨m, hm, hc⟩ := hl
        by_cases hu : u = w.next
        · rw [hu, updN_self] at hm
          simp only [Option.some.injEq] at hm
          subst hm
          have := hvxLinks c' z (hlsub c' z hc); omega
        · rw [updN_ne _ _ _ _ hu] at hm
          have := hS6 u c' z ⟨m, hm, hc⟩; omega)
      (by rw [← hN1]; exact hT1V)
      (by rw [← hN1]; exact hR1V)
  -- a space split
  have hstepS : (Nn (D + 1)).firstTime ≠ some c.i → (Nn (D)).leaf = false →
      c.p.splitAbove < last.size →
      WriterWP (handleFullWith (fun q more => appendKlongs (D) q more) (D + 1)
        (X (D + 1)) [] last false) c w (fun _ w' =>
        TreeOK (wNode c.p base w') c.i w'.top.rootKey ∧
        ((w'.top = w.top ∨ (s = 0 ∧ w.next ≤ w'.top.rootKey)) ∧ w'.taken = w.taken ∧ w'.path = w.path ∧ w.next ≤ w'.next ∧ w'.vals = w.vals) ∧
        (∀ z, z < w.next → (∀ i, s ≤ i → i ≤ D + 1 → z ≠ X i) →
          w'.nodes.lookup z = w.nodes.lookup z) ∧
        (∀ z, TReach (wNode c.p base w') c.i w'.top.rootKey z →
          TReach (updN (wNode c.p base w) (X (D + 1)) (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode)) c.i w.top.rootKey z ∨ w.next ≤ z)) := by
    intro hfirst hql hsp
    obtain ⟨r, hsc, hdiv, hf, hs, hrng⟩ := hhalves hsp
    apply writerWP_handleFullWith_space_up_last (D) (X (D + 1)) (X (D)) (Nn (D + 1))
      (Nn (D)) (K (D + 1)) last c w hlk hlq hql hfirst hsp hpq hpk
    intro w1 h1n h1t h1top h1path h1next h1vals
    obtain ⟨out, hout⟩ : ∃ o, halves (Nn (D + 1)).leaf c.i last [] = o :=
      ⟨_, rfl⟩
    rw [hout] at h1n hdiv hf hs ⊢
    rw [hdiv]
    have h12 : w.next ≠ w.next + 2 := by omega
    have hN1 : wNode c.p base w1 = updN (updN (wNode c.p base w) w.next out.1) (w.next + 2) out.2.1 :=
      wNode_two_updN c.p base w w1 _ _ _ _ h1n h1t h12 htk0 htk2'
    have hq1wf := KNode.add_key_wf (Nn (D)) c.i (K (D + 1)) w.next hqwf
    have hq1t := KNode.add_times (Nn (D)) c.i (.key (K (D + 1)) w.next)
      (fun s h => by cases h) hqtimes
    have hqlinks : ∀ c' z, (c', z) ∈ ([(K (D + 1), w.next), (r, w.next + 2)].foldl
        (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (D))).liveAt c.i →
        (c' = r ∧ z = w.next + 2) ∨ (c' ≠ r ∧ c' = K (D + 1) ∧ z = w.next) ∨
        (c' ≠ r ∧ c' ≠ K (D + 1) ∧ (c', z) ∈ (Nn (D)).liveAt c.i) := by
      intro c' z h
      simp only [List.foldl_cons, List.foldl_nil] at h
      rcases KNode.add_key_liveAt_mem _ c.i _ _ hq1wf hq1t c' z h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨h1, h2⟩
      · rcases KNode.add_key_liveAt_mem _ c.i _ _ hqwf hqtimes c' z h2 with ⟨h3, h4⟩ | ⟨h3, h4⟩
        · exact Or.inr (Or.inl ⟨h1, h3, h4⟩)
        · exact Or.inr (Or.inr ⟨h1, h3, h4⟩)
    have hXn1 : X (D + 1) ≠ w.next := by
      have := hXlt (D + 1) (by omega) (Nat.le_refl _); omega
    have hXn2 : X (D + 1) ≠ w.next + 2 := by
      have := hXlt (D + 1) (by omega) (Nat.le_refl _); omega
    have hQn1 : X (D) ≠ w.next := by have := hXlt (D) (by omega) (by omega); omega
    have hQn2 : X (D) ≠ w.next + 2 := by have := hXlt (D) (by omega) (by omega); omega
    obtain ⟨hT1V, hR1V⟩ := treeOK_spaceSplit_gen (updN (wNode c.p base w) (X (D + 1))
        (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode))
      (updN (wNode c.p base w1) (X (D)) ([(K (D + 1), w.next), (r, w.next + 2)].foldl
        (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (D)))) c.i w.top.rootKey (X (D))
      (X (D + 1)) w.next (w.next + 2) (Nn (D))
      (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode) out.1 out.2.1
      ([(K (D + 1), w.next), (r, w.next + 2)].foldl
        (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (D)))
      (K (D + 1)) r (splitLocalCv (Nn (D + 1)).leaf r) hV hqR
      (by rw [updN_ne _ _ _ _ hqx]; exact hwq) hkl (updN_self _ _ _) (updN_self _ _ _) hqlinks
      (by rw [updN_ne _ _ _ _ hQn1.symm, hN1, updN_ne _ _ _ _ h12]; exact updN_self _ _ _)
      (by rw [updN_ne _ _ _ _ hQn2.symm, hN1]; exact updN_self _ _ _)
      hf hs
      (by
        intro z hz1 hz2 hz3 hz4
        rw [updN_ne _ _ _ _ hz2, hN1, updN_ne _ _ _ _ hz4, updN_ne _ _ _ _ hz3]
        exact (updN_ne _ _ _ _ hz1).symm)
      (by rw [updN_ne _ _ _ _ hXn1.symm]; exact hwnext)
      (by rw [updN_ne _ _ _ _ hXn2.symm]; exact hwnext2)
      h12
      (by
        intro z hz
        rcases hz with hz | hz <;> rw [hz]
        · exact hVfresh w.next (Nat.le_refl _)
        · exact hVfresh (w.next + 2) (by omega))
    have hrK := hrng (by simpa using hql)
    apply hfinish w1 [(K (D + 1), w.next), (r, w.next + 2)] _
      (fun z => z = w.next ∨ z = w.next + 2)
      (Or.inr ⟨_, _, _, _, rfl, hrK.1, fun c'' z'' hm hlt => by
        have := hrK.2 c'' z'' (by simpa using hm) hlt; exact this⟩)
      (by
        intro q hq
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with hq | hq <;> rw [hq, h1next] <;> simp <;> omega)
      h1path h1t h1top (by omega) h1vals (fun z hz => by rcases hz with hz | hz <;> omega)
      (by
        intro z hz
        rw [h1n]
        have h1' : ¬ z = w.next := by omega
        have h2' : ¬ z = w.next + 2 := by omega
        simp only [h1', h2', ↓reduceIte])
      hN1
      (by
        have hR2 : ¬ TReach (updN (wNode c.p base w) w.next out.1) c.i w.top.rootKey (w.next + 2) :=
          fun h => hyR (w.next + 2) (by omega)
            (tReach_updN_unreach _ c.i _ _ _ (hyR w.next (Nat.le_refl _)) _ h)
        exact treeOK_updN_unreach _ c.i _ _ _
          (treeOK_updN_unreach _ c.i _ _ _ hS3 (hyR w.next (Nat.le_refl _))) hR2)
      (by
        intro i h1 h2
        have hR2 : ¬ TReach (updN (wNode c.p base w) w.next out.1) c.i w.top.rootKey (w.next + 2) :=
          fun h => hyR (w.next + 2) (by omega)
            (tReach_updN_unreach _ c.i _ _ _ (hyR w.next (Nat.le_refl _)) _ h)
        obtain ⟨a, ha⟩ := (hS4 i h1 (by omega)).pathLen
        have h1r := tReach_updN_of_short _ c.i _ _ out.1 a _ ha
          (fun b hb => absurd hb.reach (hyR w.next (Nat.le_refl _)))
        obtain ⟨a', ha'⟩ := h1r.pathLen
        exact tReach_updN_of_short _ c.i _ _ _ a' _ ha' (fun b hb => absurd hb.reach hR2))
      (by
        intro z hz
        rw [h1next] at hz
        obtain ⟨a, b, d⟩ := hS5 z (by omega)
        refine ⟨?_, by rw [h1t]; exact b, d⟩
        rw [h1n]
        have h1' : ¬ z = w.next := by omega
        have h2' : ¬ z = w.next + 2 := by omega
        simp only [h1', h2', ↓reduceIte, a])
      (by
        intro u c' z hl
        rw [h1next]
        obtain ⟨m, hm, hc⟩ := hl
        by_cases hu2 : u = w.next + 2
        · rw [hu2, updN_self] at hm
          simp only [Option.some.injEq] at hm
          subst hm
          obtain ⟨c0, _, _, h3⟩ := hs c' z hc
          have := hvxLinks c0 z h3; omega
        · rw [updN_ne _ _ _ _ hu2] at hm
          by_cases hu1 : u = w.next
          · rw [hu1, updN_self] at hm
            simp only [Option.some.injEq] at hm
            subst hm
            have := hvxLinks c' z (hf c' z hc).2; omega
          · rw [updN_ne _ _ _ _ hu1] at hm
            have := hS6 u c' z ⟨m, hm, hc⟩; omega)
      (by rw [← hN1]; exact hT1V)
      (by rw [← hN1]; exact hR1V)
  -- the time split, made by the transaction or not
  have hTIME : ∀ compact : Bool,
      (!compact && decide (last.size > c.p.splitAbove)) = false →
      WriterWP (handleFullWith (fun q more => appendKlongs (D) q more) (D + 1)
        (X (D + 1)) [] last compact) c w (fun _ w' =>
        TreeOK (wNode c.p base w') c.i w'.top.rootKey ∧
        ((w'.top = w.top ∨ (s = 0 ∧ w.next ≤ w'.top.rootKey)) ∧ w'.taken = w.taken ∧
          w'.path = w.path ∧ w.next ≤ w'.next ∧ w'.vals = w.vals) ∧
        (∀ z, z < w.next → (∀ i, s ≤ i → i ≤ D + 1 → z ≠ X i) →
          w'.nodes.lookup z = w.nodes.lookup z) ∧
        (∀ z, TReach (wNode c.p base w') c.i w'.top.rootKey z →
          TReach (updN (wNode c.p base w) (X (D + 1)) (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode)) c.i w.top.rootKey z ∨ w.next ≤ z)) := by
    intro compact hcs
    by_cases hmade : (Nn (D + 1)).firstTime = some c.i
    · -- a time split in place: the node holds what the tree with the klongs put has
      refine writerWP_mono (writerWP_handleFullWith_timeInPlace_termL _ (D) (X (D + 1))
        (X (D)) (Nn (D + 1)) (Nn (D)) last compact c w hlk hlq hpq hmade hcs) ?_
      rintro _ w' ⟨h't, h'top, h'v, h'next, h'path, h'n⟩
      have hN' : wNode c.p base w' = updN (wNode c.p base w) (X (D + 1))
          ⟨(Nn (D + 1)).leaf, last.ks⟩ := wNode_upsert_updN c.p base w w' _ _ h'n h't htk
      refine ⟨by rw [hN', h'top]; exact hV, ⟨Or.inl h'top, h't, h'path, by omega, h'v⟩, ?_, ?_⟩
      · intro z _ hzX
        rw [h'n, lookup_upsert, ite_eq_right_of_eq_false _ _ (eq_false (hzX _ (by omega) (Nat.le_refl _)))]
      · intro z hz
        rw [hN', h'top] at hz
        exact Or.inl (hRV z hz)
    · exact hstepT hmade compact hcs
  -- the space split, made by the transaction or not, below an inner node or a leaf
  have hSPACE : c.p.splitAbove < last.size →
      WriterWP (handleFullWith (fun q more => appendKlongs (D) q more) (D + 1)
        (X (D + 1)) [] last false) c w (fun _ w' =>
        TreeOK (wNode c.p base w') c.i w'.top.rootKey ∧
        ((w'.top = w.top ∨ (s = 0 ∧ w.next ≤ w'.top.rootKey)) ∧ w'.taken = w.taken ∧
          w'.path = w.path ∧ w.next ≤ w'.next ∧ w'.vals = w.vals) ∧
        (∀ z, z < w.next → (∀ i, s ≤ i → i ≤ D + 1 → z ≠ X i) →
          w'.nodes.lookup z = w.nodes.lookup z) ∧
        (∀ z, TReach (wNode c.p base w') c.i w'.top.rootKey z →
          TReach (updN (wNode c.p base w) (X (D + 1)) (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode)) c.i w.top.rootKey z ∨ w.next ≤ z)) := by
    intro hsp
    by_cases hmade : (Nn (D + 1)).firstTime = some c.i
    · by_cases hqlf : (Nn (D)).leaf = true
      · -- a space split in place below a leaf: a new inner node above, the leaf repointed
        obtain ⟨r, hsc, hdiv, hf, hs, _⟩ := hhalves hsp
        have hXj := hXlt (D + 1) (by omega) (Nat.le_refl _)
        have hXq := hXlt (D) (by omega) (by omega)
        refine writerWP_mono (writerWP_handleFullWith_segSpaceInPlace_termL (D) (X (D + 1))
          (X (D)) (Nn (D + 1)) (Nn (D)) last (K (D + 1)) [] c w hlk hlq hqx hqlf
          hmade hsp hpq hpk hXj hXq hfree2) ?_
        rintro _ w' ⟨j0, hj0, h't, h'top, h'v, h'path, h'next, h'n⟩
        obtain ⟨out, hout⟩ : ∃ o, halves (Nn (D + 1)).leaf c.i
            last [] = o := ⟨_, rfl⟩
        rw [hout] at h'n hdiv hf hs
        rw [hdiv] at h'n
        obtain ⟨hq2k, hq2⟩ := KNode.repoint_link_facts (Nn (D)) c.i (X (D + 1))
          (w.next + 2) (K (D + 1)) j0 hj0 hqtimes
        have hjF : ¬ X (D + 1) = w.next := by omega
        have hjR : ¬ X (D + 1) = w.next + 2 := by omega
        have hqF : ¬ X (D) = w.next := by omega
        have hqR' : ¬ X (D) = w.next + 2 := by omega
        have hFj : ¬ w.next = X (D + 1) := by omega
        have hRj : ¬ w.next + 2 = X (D + 1) := by omega
        have hFq : ¬ w.next = X (D) := by omega
        have hRq : ¬ w.next + 2 = X (D) := by omega
        have hRF : ¬ w.next + 2 = w.next := by omega
        have hw' : ∀ z, wNode c.p base w' z =
            if z = X (D + 1) then some out.1
            else if z = X (D) then some ((Nn (D)).repoint j0 (w.next + 2))
            else if z = w.next then some out.2.1
            else if z = w.next + 2 then
              some ⟨false, [.time c.i, .key 0 (X (D + 1)), .key r w.next]⟩
            else wNode c.p base w z := by
          intro z
          by_cases h1 : z = X (D + 1)
          · subst h1; simp only [wNode, h't, htk, h'n, Bool.false_eq_true, ↓reduceIte]
          · by_cases h2 : z = X (D)
            · subst h2; simp only [wNode, h't, htq, h'n, h1, Bool.false_eq_true, ↓reduceIte]
            · by_cases h3 : z = w.next
              · subst h3
                simp only [wNode, h't, htk0, h'n, h1, h2, Bool.false_eq_true, ↓reduceIte]
              · by_cases h4 : z = w.next + 2
                · subst h4
                  simp only [wNode, h't, htk2', h'n, h1, h2, h3, Bool.false_eq_true, ↓reduceIte]
                · simp only [wNode, h't, h'n, h1, h2, h3, h4, ↓reduceIte]
        have hnd : ([(0, X (D + 1)), (r, w.next)].map Prod.fst).Nodup := by
          simp only [List.map_cons, List.map_nil, List.nodup_cons, List.mem_cons,
            List.not_mem_nil, or_false, List.nodup_nil, and_true, not_false_eq_true]
          omega
        have hrn : ∀ c' z, (c', z) ∈ (⟨false, [.time c.i, .key 0 (X (D + 1)),
            .key r w.next]⟩ : KNode).liveAt c.i →
            (c' = 0 ∧ z = X (D + 1)) ∨ (c' = r ∧ z = w.next) := by
          intro c' z h
          have h' := (mrg_newKlongs_liveAt_iff false c.i [(0, X (D + 1)), (r, w.next)]
            hnd c' z).mp h
          simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h'
          exact h'
        obtain ⟨hT2, hR2⟩ := treeOK_segSpaceInPlaceStep
          (updN (wNode c.p base w) (X (D + 1))
            (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode))
          (wNode c.p base w') c.i w.top.rootKey (X (D)) (X (D + 1)) w.next (w.next + 2)
          (Nn (D)) (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode)
          out.1 out.2.1 ⟨false, [.time c.i, .key 0 (X (D + 1)), .key r w.next]⟩
          ((Nn (D)).repoint j0 (w.next + 2))
          (K (D + 1)) r (splitLocalCv (Nn (D + 1)).leaf r) hsc hV hqR
          (by rw [updN_ne _ _ _ _ hqx]; exact hwq) hkl (updN_self _ _ _)
          (by rw [hw']; simp only [hqx, ↓reduceIte])
          hq2k hq2
          (by rw [hw']; simp only [hRj, hRq, hRF, ↓reduceIte])
          hrn
          (by rw [hw']; simp only [↓reduceIte])
          (by rw [hw']; simp only [hFj, hFq, ↓reduceIte])
          hf hs
          (by
            intro z h1 h2 h3 h4
            rw [hw']
            simp only [h1, h2, h3, h4, ↓reduceIte]
            exact (updN_ne _ _ _ _ h1).symm)
          (by
            intro z hz
            have hzn : w.next ≤ z := by rcases hz with hz | hz <;> omega
            refine ⟨?_, hVfresh z hzn⟩
            rw [updN_ne _ _ _ _ (fun h => by omega)]
            obtain ⟨a, b, d⟩ := hS5 z hzn
            simp only [wNode, b, Bool.false_eq_true, ↓reduceIte, a, d])
          (by omega)
        refine ⟨by rw [h'top]; exact hT2, ⟨Or.inl h'top, h't, h'path, by omega, h'v⟩, ?_, ?_⟩
        · intro z hz hzX
          rw [h'n]
          have h1' : ¬ z = X (D + 1) := hzX _ (by omega) (Nat.le_refl _)
          have h2' : ¬ z = X (D) := hzX _ (by omega) (by omega)
          have h3' : ¬ z = w.next := by omega
          have h4' : ¬ z = w.next + 2 := by omega
          simp only [h1', h2', h3', h4', ↓reduceIte]
        · intro z hz
          rw [h'top] at hz
          rcases hR2 z hz with h | h | h
          · exact Or.inl (hRV _ h)
          · exact Or.inr (by omega)
          · exact Or.inr (by omega)
      · -- a space split in place below an inner node: the second half linked from the parent
        obtain ⟨r, hsc, hdiv, hf, hs, _⟩ := hhalves hsp
        have hXj := hXlt (D + 1) (by omega) (Nat.le_refl _)
        have hXq := hXlt (D) (by omega) (by omega)
        apply writerWP_handleFullWith_spaceInPlace_up_last (D) (X (D + 1)) (X (D))
          (Nn (D + 1)) (Nn (D)) last c w hlk hlq (by simpa using hqlf) hmade hsp hpq hXj
        intro w1 h1n h1t h1top h1path h1next h1vals
        obtain ⟨out, hout⟩ : ∃ o, halves (Nn (D + 1)).leaf c.i
            last [] = o := ⟨_, rfl⟩
        rw [hout] at h1n hdiv hf hs ⊢
        rw [hdiv]
        have hN1 : wNode c.p base w1 = updN (updN (wNode c.p base w) (X (D + 1)) out.1)
            w.next out.2.1 :=
          wNode_two_updN c.p base w w1 _ _ _ _ h1n h1t (by omega) htk htk0
        have hVS : ¬ TReach (updN (wNode c.p base w) (X (D + 1))
            (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode))
            c.i w.top.rootKey w.next :=
          not_reach_fresh _ c.i _ _ hV (by rw [updN_ne _ _ _ _ (fun h => by omega)]; exact hwnext)
            (hVfresh w.next (Nat.le_refl _))
        obtain ⟨hTsub, hRsub⟩ := treeOK_updN_sub (wNode c.p base w) c.i w.top.rootKey
          (X (D + 1)) _ out.1 hV (fun c' z h => (hf c' z h).2)
        have hS1' : ¬ TReach (updN (wNode c.p base w) (X (D + 1)) out.1) c.i w.top.rootKey
            w.next := fun h => hVS (hRsub _ h)
        have hT1 : TreeOK (updN (updN (wNode c.p base w) (X (D + 1)) out.1) w.next out.2.1)
            c.i w.top.rootKey := treeOK_updN_unreach _ c.i _ _ _ hTsub hS1'
        have hagree1 : ∀ z, TReach (updN (wNode c.p base w) (X (D + 1)) out.1) c.i
            w.top.rootKey z → updN (updN (wNode c.p base w) (X (D + 1)) out.1) w.next out.2.1 z =
            updN (wNode c.p base w) (X (D + 1)) out.1 z :=
          fun z hz => updN_ne _ _ _ _ (fun he => hS1' (he ▸ hz))
        obtain ⟨hT2, hR2⟩ := treeOK_spaceInPlaceStep
          (updN (wNode c.p base w) (X (D + 1))
            (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode))
          (updN (wNode c.p base w1) (X (D)) ([(r, w.next)].foldl
            (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (D))))
          c.i w.top.rootKey (X (D)) (X (D + 1)) w.next
          (Nn (D)) (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode)
          out.1 out.2.1
          ([(r, w.next)].foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (D)))
          (K (D + 1)) r (splitLocalCv (Nn (D + 1)).leaf r) hV hqR
          (by rw [updN_ne _ _ _ _ hqx]; exact hwq) hkl (updN_self _ _ _) (updN_self _ _ _)
          (by
            intro c' z h
            simp only [List.foldl_cons, List.foldl_nil] at h
            exact KNode.add_key_liveAt_mem _ c.i _ _ hqwf hqtimes c' z h)
          (by
            rw [updN_ne _ _ _ _ (Ne.symm hqx), hN1, updN_ne _ _ _ _ (fun h => by omega)]
            exact updN_self _ _ _)
          (by
            rw [updN_ne _ _ _ _ (fun h => by omega), hN1]
            exact updN_self _ _ _)
          hf hs
          (by
            intro z hz1 hz2 hz3
            rw [updN_ne _ _ _ _ hz2, hN1, updN_ne _ _ _ _ hz3, updN_ne _ _ _ _ hz1]
            exact (updN_ne _ _ _ _ hz1).symm)
          (by rw [updN_ne _ _ _ _ (fun h => by omega)]; exact hwnext)
          (hVfresh w.next (Nat.le_refl _))
        have hpar := hchain w1 [(r, w.next)] (Or.inl ⟨_, _, rfl⟩)
          (by
            intro q hq
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
            rw [hq, h1next]
            show w.next < w.next + 2
            omega)
          (by rw [h1path, hS1])
          (by
            intro i h1 h2
            obtain ⟨a, b⟩ := hS2 i h1 (by omega)
            refine ⟨?_, by rw [h1t]; exact b⟩
            rw [h1n]
            have hne1 : ¬ X i = X (D + 1) := fun he => by
              have := hdist _ _ h1 (by omega) (by omega) (Nat.le_refl _) he; omega
            have hne2 : ¬ X i = w.next := by have := hXlt i h1 (by omega); omega
            simp only [hne1, hne2, ↓reduceIte, a])
          (by rw [hN1, h1top]; exact hT1)
          (by
            intro i h1 h2
            rw [hN1, h1top]
            exact tReach_to_agree _ _ c.i _ hagree1 _ (hanc out.1 i h1 h2))
          (by
            intro z hz
            rw [h1next] at hz
            obtain ⟨a, b, d⟩ := hS5 z (by omega)
            refine ⟨?_, by rw [h1t]; exact b, d⟩
            rw [h1n]
            have h1' : ¬ z = X (D + 1) := by omega
            have h2' : ¬ z = w.next := by omega
            simp only [h1', h2', ↓reduceIte, a])
          (by
            intro u c' z hl
            rw [h1next]
            obtain ⟨m, hm, hc⟩ := hl
            rw [hN1] at hm
            by_cases hu2 : u = w.next
            · rw [hu2, updN_self] at hm
              simp only [Option.some.injEq] at hm
              subst hm
              obtain ⟨c0, _, _, h3⟩ := hs c' z hc
              have := hvxLinks c0 z h3; omega
            · rw [updN_ne _ _ _ _ hu2] at hm
              by_cases hu1 : u = X (D + 1)
              · rw [hu1, updN_self] at hm
                simp only [Option.some.injEq] at hm
                subst hm
                have := hvxLinks c' z (hf c' z hc).2; omega
              · rw [updN_ne _ _ _ _ hu1] at hm
                have := hS6 u c' z ⟨m, hm, hc⟩; omega)
          (fun h0 => by rw [h1top]; exact hR0 h0)
          (by rw [h1top]; exact hT2)
        refine writerWP_mono hpar ?_
        rintro _ w2 ⟨hT2', ⟨h2top, h2t, h2path, h2next, h2vals⟩, h2frame, h2reach⟩
        refine ⟨hT2', ⟨?_, by rw [h2t, h1t], by rw [h2path, h1path], by omega,
          by rw [h2vals, h1vals]⟩, ?_, ?_⟩
        · rcases h2top with h | ⟨h0, h⟩
          · exact Or.inl (h.trans h1top)
          · exact Or.inr ⟨h0, by omega⟩
        · intro z hz hzX
          rw [h2frame z (by omega) (fun i h1 h2 => hzX i h1 (by omega)), h1n]
          have h1' : ¬ z = X (D + 1) := hzX _ (by omega) (Nat.le_refl _)
          have h2' : ¬ z = w.next := by omega
          simp only [h1', h2', ↓reduceIte]
        · intro z hz
          rcases h2reach z hz with h' | h'
          · rw [h1top] at h'
            rcases hR2 z h' with h'' | h''
            · exact Or.inl (hRV _ h'')
            · exact Or.inr (by omega)
          · exact Or.inr (by omega)
    · by_cases hqlf : (Nn (D)).leaf = true
      · -- a space split below a leaf, the node not made: a new inner node above the halves
        obtain ⟨r, hsc, hdiv, hf, hs, _⟩ := hhalves hsp
        apply writerWP_handleFullWith_segSpace_upL (D) (X (D + 1)) (X (D))
          (Nn (D + 1)) (Nn (D)) last (K (D + 1)) [] c w hlk hlq hqlf hmade hsp hpq hpk
        intro w1 h1n h1t h1top h1path h1next h1vals
        obtain ⟨out, hout⟩ : ∃ o, halves (Nn (D + 1)).leaf c.i
            last [] = o := ⟨_, rfl⟩
        rw [hout] at h1n hdiv hf hs
        rw [hdiv] at h1n
        obtain ⟨hfree4, htk4, hbase4⟩ := hS5 (w.next + 2 + 2) (by omega)
        have hN1 : wNode c.p base w1 = updN (updN (updN (wNode c.p base w) w.next out.1)
            (w.next + 2) out.2.1) (w.next + 2 + 2)
            ⟨false, [.time c.i, .key 0 w.next, .key r (w.next + 2)]⟩ :=
          wNode_three_updN c.p base w w1 _ _ _ _ _ _ h1n h1t (by omega) (by omega) (by omega)
            htk0 htk2' htk4
        have h1low : ∀ z, z < w.next → w1.nodes.lookup z = w.nodes.lookup z := by
          intro z hz
          rw [h1n]
          have h1' : ¬ z = w.next := by omega
          have h2' : ¬ z = w.next + 2 := by omega
          have h3' : ¬ z = w.next + 2 + 2 := by omega
          simp only [h1', h2', h3', ↓reduceIte]
        have hagree : ∀ z, TReach (wNode c.p base w) c.i w.top.rootKey z →
            wNode c.p base w1 z = wNode c.p base w z := by
          intro z hz
          rcases Nat.lt_or_ge z w.next with h | h
          · exact wNode_low_agree c.p base w w1 h1t h1low z h
          · exact absurd hz (hyR z h)
        have hnd : ([(0, w.next), (r, w.next + 2)].map Prod.fst).Nodup := by
          simp only [List.map_cons, List.map_nil, List.nodup_cons, List.mem_cons,
            List.not_mem_nil, or_false, List.nodup_nil, and_true, not_false_eq_true]
          omega
        have hrn : ∀ c' z, (c', z) ∈ (⟨false, [.time c.i, .key 0 w.next, .key r (w.next + 2)]⟩ :
            KNode).liveAt c.i → (c' = 0 ∧ z = w.next) ∨ (c' = r ∧ z = w.next + 2) := by
          intro c' z h
          have h' := (mrg_newKlongs_liveAt_iff false c.i [(0, w.next), (r, w.next + 2)] hnd c' z).mp h
          simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h'
          exact h'
        have hXj := hXlt (D + 1) (by omega) (Nat.le_refl _)
        have hXq := hXlt (D) (by omega) (by omega)
        obtain ⟨hT2, hR2⟩ := treeOK_segSpaceStep
          (updN (wNode c.p base w) (X (D + 1))
            (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode))
          (updN (wNode c.p base w1) (X (D)) ([(K (D + 1), w.next + 2 + 2)].foldl
            (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (D))))
          c.i w.top.rootKey (X (D)) (X (D + 1)) w.next (w.next + 2) (w.next + 2 + 2)
          (Nn (D)) (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode)
          out.1 out.2.1 ⟨false, [.time c.i, .key 0 w.next, .key r (w.next + 2)]⟩
          ([(K (D + 1), w.next + 2 + 2)].foldl
            (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (D)))
          (K (D + 1)) r (splitLocalCv (Nn (D + 1)).leaf r) hsc hV hqR
          (by rw [updN_ne _ _ _ _ hqx]; exact hwq) hkl (updN_self _ _ _) (updN_self _ _ _)
          (KNode.add_key_liveAt_self _ c.i _ _ hqwf hqtimes)
          (by
            intro c' z h
            simp only [List.foldl_cons, List.foldl_nil] at h
            exact KNode.add_key_liveAt_mem _ c.i _ _ hqwf hqtimes c' z h)
          (by
            rw [updN_ne _ _ _ _ (fun h => by omega), hN1]
            exact updN_self _ _ _)
          hrn
          (by
            rw [updN_ne _ _ _ _ (fun h => by omega), hN1,
              updN_ne _ _ _ _ (fun h => by omega), updN_ne _ _ _ _ (fun h => by omega)]
            exact updN_self _ _ _)
          (by
            rw [updN_ne _ _ _ _ (fun h => by omega), hN1, updN_ne _ _ _ _ (fun h => by omega)]
            exact updN_self _ _ _)
          hf hs
          (by
            intro z hz1 hz2 hz3 hz4 hz5
            rw [updN_ne _ _ _ _ hz2, hN1, updN_ne _ _ _ _ hz5, updN_ne _ _ _ _ hz4,
              updN_ne _ _ _ _ hz3]
            exact (updN_ne _ _ _ _ hz1).symm)
          (by
            intro z hz
            have hzn : w.next ≤ z := by rcases hz with hz | hz | hz <;> omega
            refine ⟨?_, hVfresh z hzn⟩
            rw [updN_ne _ _ _ _ (fun h => by omega)]
            obtain ⟨a, b, d⟩ := hS5 z hzn
            simp only [wNode, b, Bool.false_eq_true, ↓reduceIte, a, d])
          (by omega) (by omega) (by omega)
        apply hfinish w1 [(K (D + 1), w.next + 2 + 2)] (wNode c.p base w1)
          (fun z => z = w.next ∨ z = w.next + 2 ∨ z = w.next + 2 + 2)
          (Or.inl ⟨_, _, rfl⟩)
          (by
            intro q hq
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
            rw [hq, h1next]
            show w.next + 2 + 2 < w.next + 2 + 2 + 2
            omega)
          h1path h1t h1top (by omega) h1vals
          (fun z hz => by rcases hz with hz | hz | hz <;> omega)
          h1low rfl (treeOK_of_agree _ _ _ _ hS3 hagree)
          (fun i h1 h2 => tReach_to_agree _ _ _ _ hagree _ (hS4 i h1 (by omega)))
          (by
            intro z hz
            rw [h1next] at hz
            obtain ⟨a, b, d⟩ := hS5 z (by omega)
            refine ⟨?_, by rw [h1t]; exact b, d⟩
            rw [h1n]
            have h1' : ¬ z = w.next := by omega
            have h2' : ¬ z = w.next + 2 := by omega
            have h3' : ¬ z = w.next + 2 + 2 := by omega
            simp only [h1', h2', h3', ↓reduceIte, a])
          (by
            intro u c' z hl
            rw [h1next]
            obtain ⟨m, hm, hc⟩ := hl
            rw [hN1] at hm
            by_cases hu3 : u = w.next + 2 + 2
            · rw [hu3, updN_self] at hm
              simp only [Option.some.injEq] at hm
              subst hm
              rcases hrn c' z hc with ⟨_, h⟩ | ⟨_, h⟩ <;> omega
            · rw [updN_ne _ _ _ _ hu3] at hm
              by_cases hu2 : u = w.next + 2
              · rw [hu2, updN_self] at hm
                simp only [Option.some.injEq] at hm
                subst hm
                obtain ⟨c0, _, _, h3⟩ := hs c' z hc
                have := hvxLinks c0 z h3; omega
              · rw [updN_ne _ _ _ _ hu2] at hm
                by_cases hu1 : u = w.next
                · rw [hu1, updN_self] at hm
                  simp only [Option.some.injEq] at hm
                  subst hm
                  have := hvxLinks c' z (hf c' z hc).2; omega
                · rw [updN_ne _ _ _ _ hu1] at hm
                  have := hS6 u c' z ⟨m, hm, hc⟩; omega)
          hT2 hR2
      · exact hstepS hmade (by simpa using hqlf) hsp
  by_cases hsp : c.p.splitAbove < last.size ∧ compact = false
  · obtain ⟨hsp, hc⟩ := hsp
    subst hc
    exact hSPACE hsp
  · apply hTIME compact
    cases compact with
    | true => simp
    | false =>
      simp only [Bool.not_false, Bool.true_and, decide_eq_false_iff_not, gt_iff_lt]
      exact fun h => hsp ⟨h, rfl⟩

end SIS.Tree
