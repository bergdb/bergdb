/-
The merge's tail where its parent goes `full` and splits in space with a cascade
(bergdb 030-01, step 3's rest): a space split leaves no hole, so the parent's
klongs to the halves go up through `writerWP_appendKlongs_chainGL` whatever the
room above, as for the delete's full leaf (l4b's `writerWP_handleFull_segSpaceChain_live`,
LiveDelSpaceChain2.lean), here on the merged tree (the parent's node replaced by
its last version). The split is given to the space tail as `SplitStepOKW`
(LiveMergeSpace.lean). The rest is `MergeTailFullRest7OK`.
-/
import SIS.Tree.LiveMergeRoot
import SIS.Tree.LiveDelSpaceChain2

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

set_option maxHeartbeats 8000000 in
/-- l4b's `writerWP_handleFull_segSpaceChain_live` (LiveDelSpaceChain2.lean) on the
tree V with the segment root X (D + 1)'s node replaced by its last version (the
merge's parent's): from V's live counts, with halves that are `HalfOK` and hold V's
node's live klongs, they hold after, the cascade's top split or not, and the nodes
reached after were reached in V or are new, not X (D + 1). -/
theorem writerWP_handleFull_segSpaceChainV_live (c : Ctx) (base : View BVal)
    (path0 : List (Option Nat × NodeId)) (D : Nat) (X : Nat → NodeId) (K : Nat → Nat)
    (Nn : Nat → KNode) (last : KNode)
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
    (hfirst : (Nn (D + 1)).firstTime ≠ some c.i) (hql : (Nn D).leaf = true)
    (hsplit : c.p.splitAbove < last.size)
    (hsc : 0 < (halves (Nn (D + 1)).leaf c.i last []).2.2)
    (hf : ∀ c' z, (c', z) ∈ (halves (Nn (D + 1)).leaf c.i last []).1.liveAt c.i →
      c' < (halves (Nn (D + 1)).leaf c.i last []).2.2 ∧ (c', z) ∈ (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode).liveAt c.i)
    (hs : ∀ c' z, (c', z) ∈ (halves (Nn (D + 1)).leaf c.i last []).2.1.liveAt c.i →
      ∃ c0, (halves (Nn (D + 1)).leaf c.i last []).2.2 ≤ c0 ∧
        c' = splitLocalCv (Nn (D + 1)).leaf (halves (Nn (D + 1)).leaf c.i last []).2.2 c0 ∧
        (c0, z) ∈ (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode).liveAt c.i)
    (hfH : HalfOK c.p c.i (halves (Nn (D + 1)).leaf c.i last []).1)
    (hsH : HalfOK c.p c.i (halves (Nn (D + 1)).leaf c.i last []).2.1)
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
    (hqRV : TReach (updN (wNode c.p base w) (X (D + 1)) ⟨(Nn (D + 1)).leaf, last.ks⟩) c.i w.top.rootKey (X D))
    (hlinksV : ∀ u c' z, TReach (updN (wNode c.p base w) (X (D + 1)) ⟨(Nn (D + 1)).leaf, last.ks⟩) c.i w.top.rootKey u →
      TLink (updN (wNode c.p base w) (X (D + 1)) ⟨(Nn (D + 1)).leaf, last.ks⟩) c.i u c' z → z < w.next)
    (hLV : LiveEdges c.p (updN (wNode c.p base w) (X (D + 1)) ⟨(Nn (D + 1)).leaf, last.ks⟩) c.i w.top.rootKey) :
    WriterWP (handleFullWith (fun q more => appendKlongs D q more) (D + 1) (X (D + 1)) [] last
      false) c w (fun _ w' => LiveEdges c.p (wNode c.p base w') c.i w'.top.rootKey ∧
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
  have hnoLink : ∀ z, w.next ≤ z → ∀ u c', ¬ TLink (wNode c.p base w) c.i u c' z := by
    intro z hz u c' hl; have := hS6 u c' z hl; omega
  have hwz : ∀ z, w.next ≤ z → wNode c.p base w z = none := by
    intro z hz
    obtain ⟨a, b, d⟩ := hS5 z hz
    simp only [wNode, b, Bool.false_eq_true, ↓reduceIte, a, d]
  have hyR : ∀ z, w.next ≤ z → ¬ TReach (wNode c.p base w) c.i w.top.rootKey z :=
    fun z hz => not_reach_fresh _ c.i _ z hS3 (hwz z hz) (fun u c' _ => hnoLink z hz u c')
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
  have hqV : (updN (wNode c.p base w) (X (D + 1)) ⟨(Nn (D + 1)).leaf, last.ks⟩) (X D) = some (Nn D) := by rw [updN_ne _ _ _ _ hqx]; exact hwq
  have hxV : (updN (wNode c.p base w) (X (D + 1)) ⟨(Nn (D + 1)).leaf, last.ks⟩) (X (D + 1)) = some (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode) := updN_self _ _ _
  have hxRV : TReach (updN (wNode c.p base w) (X (D + 1)) ⟨(Nn (D + 1)).leaf, last.ks⟩) c.i w.top.rootKey (X (D + 1)) := TReach.link hqRV ⟨Nn D, hqV, hkl⟩
  have hqwf := hwf D (by omega)
  have hqtimes := htimes D (by omega)
  have hXn1 : X (D + 1) ≠ w.next := by have := hXlt (D + 1) (Nat.le_refl _); omega
  have hXn2 : X (D + 1) ≠ w.next + 2 := by have := hXlt (D + 1) (Nat.le_refl _); omega
  have hXn3 : X (D + 1) ≠ w.next + 2 + 2 := by have := hXlt (D + 1) (Nat.le_refl _); omega
  have hQn1 : X D ≠ w.next := by have := hXlt D (by omega); omega
  have hQn2 : X D ≠ w.next + 2 := by have := hXlt D (by omega); omega
  have hQn3 : X D ≠ w.next + 2 + 2 := by have := hXlt D (by omega); omega
  apply writerWP_handleFullWith_segSpace_upL D (X (D + 1)) (X D) (Nn (D + 1)) (Nn D) last (K (D + 1))
    [] c w hlk hlq hql hfirst hsplit hpq hpk
  intro w1 h1n h1t h1top h1path h1next h1vals
  obtain ⟨hfl, hsl⟩ := halves_leaf_eq (Nn (D + 1)).leaf c.i last []
  generalize hout : halves (Nn (D + 1)).leaf c.i last [] = out at hsc hf hs hfH hsH hfl hsl h1n ⊢
  have h12 : w.next ≠ w.next + 2 := by omega
  have h13 : w.next ≠ w.next + 2 + 2 := by omega
  have h23 : w.next + 2 ≠ w.next + 2 + 2 := by omega
  have hN1 : wNode c.p base w1 = updN (updN (updN (wNode c.p base w) w.next out.1) (w.next + 2)
      out.2.1) (w.next + 2 + 2) ⟨false, [.time c.i, .key 0 w.next, .key out.2.2 (w.next + 2)]⟩ := by
    funext z
    unfold wNode updN
    rw [h1t, h1n z]
    by_cases h3 : z = w.next + 2 + 2
    · subst h3
      simp only [Ne.symm h13, Ne.symm h23, (hS5 (w.next + 2 + 2) (by omega)).2.1, Bool.false_eq_true,
        ↓reduceIte]
    · simp only [h3, ↓reduceIte]
      by_cases h2 : z = w.next + 2
      · subst h2
        simp only [Ne.symm h12, (hS5 (w.next + 2) (by omega)).2.1, Bool.false_eq_true, ↓reduceIte]
      · simp only [h2, ↓reduceIte]
        by_cases h1 : z = w.next
        · subst h1; simp only [(hS5 w.next (Nat.le_refl _)).2.1, Bool.false_eq_true, ↓reduceIte]
        · simp only [h1, ↓reduceIte]
  have hat := KNode.add_times (Nn D) c.i (.key (K (D + 1)) (w.next + 2 + 2)) (fun s h => by cases h) hqtimes
  have hq2k : (K (D + 1), w.next + 2 + 2) ∈ ([(K (D + 1), w.next + 2 + 2)].foldl
      (fun n (cv, y) => n.add c.i (.key cv y)) (Nn D)).liveAt c.i := by
    simp only [List.foldl_cons, List.foldl_nil]
    rw [KNode.liveAt_of_times _ c.i hat]
    apply bk_mem_of_lookup
    rw [KNode.add_key_live_lookup_of_wf (Nn D) c.i (K (D + 1)) (K (D + 1)) (w.next + 2 + 2) hqwf]
    simp
  have hq2 : ∀ c' z, (c', z) ∈ ([(K (D + 1), w.next + 2 + 2)].foldl
      (fun n (cv, y) => n.add c.i (.key cv y)) (Nn D)).liveAt c.i →
      (c' = K (D + 1) ∧ z = w.next + 2 + 2) ∨ (c' ≠ K (D + 1) ∧ (c', z) ∈ (Nn D).liveAt c.i) := by
    intro c' z h
    simp only [List.foldl_cons, List.foldl_nil] at h
    exact KNode.add_key_liveAt_mem _ c.i _ _ hqwf hqtimes c' z h
  have hq2l : ([(K (D + 1), w.next + 2 + 2)].foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn D)).leaf =
      (Nn D).leaf := by
    simp only [List.foldl_cons, List.foldl_nil, KNode.add_leaf]
  have hnd : ([(0, w.next), (out.2.2, w.next + 2)].map Prod.fst).Nodup := by
    simp only [List.map_cons, List.map_nil, List.nodup_cons, List.mem_cons,
      List.not_mem_nil, or_false, List.nodup_nil, and_true, not_false_eq_true]
    omega
  have hrn : ∀ c' z, (c', z) ∈ (⟨false, [.time c.i, .key 0 w.next, .key out.2.2 (w.next + 2)]⟩ :
      KNode).liveAt c.i → (c' = 0 ∧ z = w.next) ∨ (c' = out.2.2 ∧ z = w.next + 2) := by
    intro c' z h
    have h' := (mrg_newKlongs_liveAt_iff false c.i [(0, w.next), (out.2.2, w.next + 2)] hnd c'
      z).mp h
    simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h'
    exact h'
  have hN'q : updN (wNode c.p base w1) (X D) ([(K (D + 1), w.next + 2 + 2)].foldl
      (fun n (cv, y) => n.add c.i (.key cv y)) (Nn D)) (X D) = some ([(K (D + 1), w.next + 2 + 2)].foldl
      (fun n (cv, y) => n.add c.i (.key cv y)) (Nn D)) := updN_self _ _ _
  have hN'F : updN (wNode c.p base w1) (X D) ([(K (D + 1), w.next + 2 + 2)].foldl
      (fun n (cv, y) => n.add c.i (.key cv y)) (Nn D)) w.next = some out.1 := by
    rw [updN_ne _ _ _ _ hQn1.symm, hN1, updN_ne _ _ _ _ h13, updN_ne _ _ _ _ h12]
    exact updN_self _ _ _
  have hN'S : updN (wNode c.p base w1) (X D) ([(K (D + 1), w.next + 2 + 2)].foldl
      (fun n (cv, y) => n.add c.i (.key cv y)) (Nn D)) (w.next + 2) = some out.2.1 := by
    rw [updN_ne _ _ _ _ hQn2.symm, hN1, updN_ne _ _ _ _ h23]
    exact updN_self _ _ _
  have hN'R : updN (wNode c.p base w1) (X D) ([(K (D + 1), w.next + 2 + 2)].foldl
      (fun n (cv, y) => n.add c.i (.key cv y)) (Nn D)) (w.next + 2 + 2) =
      some ⟨false, [.time c.i, .key 0 w.next, .key out.2.2 (w.next + 2)]⟩ := by
    rw [updN_ne _ _ _ _ hQn3.symm, hN1]
    exact updN_self _ _ _
  have hoth : ∀ z, z ≠ X (D + 1) → z ≠ X D → z ≠ w.next → z ≠ w.next + 2 → z ≠ w.next + 2 + 2 →
      updN (wNode c.p base w1) (X D) ([(K (D + 1), w.next + 2 + 2)].foldl
        (fun n (cv, y) => n.add c.i (.key cv y)) (Nn D)) z = (updN (wNode c.p base w) (X (D + 1)) ⟨(Nn (D + 1)).leaf, last.ks⟩) z := by
    intro z hz1 hz2 hz3 hz4 hz5
    rw [updN_ne _ _ _ _ hz2, hN1, updN_ne _ _ _ _ hz5, updN_ne _ _ _ _ hz4, updN_ne _ _ _ _ hz3,
      updN_ne _ _ _ _ hz1]
  have hfreshV : ∀ z, (z = w.next ∨ z = w.next + 2 ∨ z = w.next + 2 + 2) →
      (updN (wNode c.p base w) (X (D + 1)) ⟨(Nn (D + 1)).leaf, last.ks⟩) z = none ∧ ∀ u c', TReach (updN (wNode c.p base w) (X (D + 1)) ⟨(Nn (D + 1)).leaf, last.ks⟩) c.i w.top.rootKey u →
        ¬ TLink (updN (wNode c.p base w) (X (D + 1)) ⟨(Nn (D + 1)).leaf, last.ks⟩) c.i u c' z := by
    intro z hz
    have hzn : w.next ≤ z := by rcases hz with hz | hz | hz <;> omega
    refine ⟨by rw [updN_ne _ _ _ _ (by have := hXlt (D + 1) (Nat.le_refl _); omega)]; exact hwz z hzn,
      fun u c' hu hl => ?_⟩
    have := hlinksV u c' z hu hl
    omega
  obtain ⟨hT1V, hR1V⟩ := treeOK_segSpaceStep (updN (wNode c.p base w) (X (D + 1)) ⟨(Nn (D + 1)).leaf, last.ks⟩)
    (updN (wNode c.p base w1) (X D) ([(K (D + 1), w.next + 2 + 2)].foldl
      (fun n (cv, y) => n.add c.i (.key cv y)) (Nn D))) c.i w.top.rootKey (X D) (X (D + 1))
    w.next (w.next + 2) (w.next + 2 + 2) (Nn D) (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode) out.1 out.2.1
    ⟨false, [.time c.i, .key 0 w.next, .key out.2.2 (w.next + 2)]⟩
    ([(K (D + 1), w.next + 2 + 2)].foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn D))
    (K (D + 1)) out.2.2 (splitLocalCv (Nn (D + 1)).leaf out.2.2) hsc hTV hqRV hqV hkl
    hxV hN'q hq2k hq2 hN'R hrn hN'F hN'S hf hs hoth hfreshV h12 h13 h23
  have hLV := liveEdgesX_segSpaceStep c.p (fun _ => False) (updN (wNode c.p base w) (X (D + 1)) ⟨(Nn (D + 1)).leaf, last.ks⟩)
    (updN (wNode c.p base w1) (X D) ([(K (D + 1), w.next + 2 + 2)].foldl
      (fun n (cv, y) => n.add c.i (.key cv y)) (Nn D))) c.i w.top.rootKey (X D) (X (D + 1))
    w.next (w.next + 2) (w.next + 2 + 2) (Nn D) (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode) out.1 out.2.1
    ⟨false, [.time c.i, .key 0 w.next, .key out.2.2 (w.next + 2)]⟩
    ([(K (D + 1), w.next + 2 + 2)].foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn D))
    (K (D + 1)) out.2.2 (splitLocalCv (Nn (D + 1)).leaf out.2.2) hsc hTV hqRV hqV hkl
    hxV hN'q hq2k hq2 hN'R hrn hN'F hN'S hf hs hoth hfreshV h12 h13 h23
    (fun h => h) (fun h => h) (fun h => h) hfl hsl hfH hsH
    (newRoot_liveAt_two c.i w.next (w.next + 2) out.2.2 hsc) (by rw [hq2l]; exact hql) hq2l
    (addKeys_liveAt_length c.i [(K (D + 1), w.next + 2 + 2)] (Nn D) hqwf hqtimes)
    ((liveEdgesX_false_iff _ _ _ _).mpr hLV)
  have hR2 : ¬ TReach (updN (wNode c.p base w) w.next out.1) c.i w.top.rootKey (w.next + 2) :=
    fun h => hyR (w.next + 2) (by omega)
      (tReach_updN_unreach _ c.i _ _ _ (hyR w.next (Nat.le_refl _)) _ h)
  have hR3 : ¬ TReach (updN (updN (wNode c.p base w) w.next out.1) (w.next + 2) out.2.1) c.i
      w.top.rootKey (w.next + 2 + 2) :=
    fun h => hyR (w.next + 2 + 2) (by omega)
      (tReach_updN_unreach _ c.i _ _ _ (hyR w.next (Nat.le_refl _)) _
        (tReach_updN_unreach _ c.i _ _ _ hR2 _ h))
  have hpar := hchain w1 [(K (D + 1), w.next + 2 + 2)] (Or.inl ⟨_, _, rfl⟩)
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
      have h1' : ¬ X i = w.next := by have := hXlt i (by omega); omega
      have h2' : ¬ X i = w.next + 2 := by have := hXlt i (by omega); omega
      have h3' : ¬ X i = w.next + 2 + 2 := by have := hXlt i (by omega); omega
      simp only [h1', h2', h3', ↓reduceIte, a])
    (by
      rw [hN1, h1top]
      exact treeOK_updN_unreach _ c.i _ _ _ (treeOK_updN_unreach _ c.i _ _ _
        (treeOK_updN_unreach _ c.i _ _ _ hS3 (hyR w.next (Nat.le_refl _))) hR2) hR3)
    (by
      intro i _ h2
      rw [hN1, h1top]
      obtain ⟨a, ha⟩ := (hS4 i (by omega)).pathLen
      have h1r := tReach_updN_of_short _ c.i _ _ out.1 a _ ha
        (fun b hb => absurd hb.reach (hyR w.next (Nat.le_refl _)))
      obtain ⟨a', ha'⟩ := h1r.pathLen
      have h2r := tReach_updN_of_short _ c.i _ _ out.2.1 a' _ ha' (fun b hb => absurd hb.reach hR2)
      obtain ⟨a'', ha''⟩ := h2r.pathLen
      exact tReach_updN_of_short _ c.i _ _ _ a'' _ ha'' (fun b hb => absurd hb.reach hR3))
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
      rw [hN1] at hl
      obtain ⟨m, hm, hc⟩ := hl
      by_cases hu3 : u = w.next + 2 + 2
      · rw [hu3, updN_self] at hm
        simp only [Option.some.injEq] at hm
        subst hm
        rcases hrn c' z hc with ⟨_, hz⟩ | ⟨_, hz⟩ <;> omega
      · rw [updN_ne _ _ _ _ hu3] at hm
        by_cases hu2 : u = w.next + 2
        · rw [hu2, updN_self] at hm
          simp only [Option.some.injEq] at hm
          subst hm
          obtain ⟨c0, _, _, h3⟩ := hs c' z hc
          have := hlinksV _ c0 z hxRV ⟨_, hxV, h3⟩; omega
        · rw [updN_ne _ _ _ _ hu2] at hm
          by_cases hu1 : u = w.next
          · rw [hu1, updN_self] at hm
            simp only [Option.some.injEq] at hm
            subst hm
            have := hlinksV _ c' z hxRV ⟨_, hxV, (hf c' z hc).2⟩; omega
          · rw [updN_ne _ _ _ _ hu1] at hm
            have := hS6 u c' z ⟨m, hm, hc⟩; omega)
    (fun _ => by rw [h1top]; exact hR0)
    (by rw [h1top]; exact hT1V)
  refine writerWP_mono hpar ?_
  rintro _ w2 ⟨_, ⟨_, h2t, _, _, _⟩, h2frame, h2reach, h2live⟩
  have hlk2 : w2.nodes.lookup (X (D + 1)) = some (Nn (D + 1)) := by
    rw [h2frame _ (by have := hXlt (D + 1) (Nat.le_refl _); omega)
      (fun i _ h2 he => by have := hdist _ _ (Nat.le_refl _) (by omega) he; omega)]
    rw [h1n]
    simp only [hXn1, hXn2, hXn3, ↓reduceIte, hlk]
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
        refine ⟨?_, h2⟩
        rcases h1 with h | h | h | h
        · exact Or.inl h
        · exact Or.inr (by omega)
        · exact Or.inr (by omega)
        · exact Or.inr (by omega)
      · rw [h1next] at h'
        have := hXlt (D + 1) (Nat.le_refl _)
        exact ⟨Or.inr (by omega), by omega⟩
  exact key _ rfl rfl rfl

/-- The instance of `SplitStepOKW` for a segment root p below its segment leaf q,
whatever q's room (the cascade): l4b's segment-root split and its cascade on the
merged tree (`writerWP_handleFull_segSpaceChainV_live`), with the path's facts at
the merge's start w3 (`PathOK` down to p) and w3's tree. -/
theorem splitStepOKW_segChain (c : Ctx) (base : View BVal) (hmp : MergeParamsOK c.p) (d' : Nat)
    (p q : NodeId) (pn qn : KNode) (k1 : Nat) (w3 : W) (x : NodeId)
    (X : Nat → NodeId) (K : Nat → Nat) (Nn : Nat → KNode)
    (hP : PathOK c w3 (d' + 1) X K Nn)
    (hXp : X (d' + 1) = p) (hXq : X d' = q) (hNp : Nn (d' + 1) = pn) (hNq : Nn d' = qn)
    (hpnew : pn.firstTime ≠ some c.i) (hql : qn.leaf = true)
    (hxX : ∀ i, i ≤ d' + 1 → X i ≠ x) (hXlt : ∀ i, i ≤ d' + 1 → X i < w3.next)
    (hT3 : TreeOK (wNode c.p base w3) c.i w3.top.rootKey)
    (hRO : RangeOrder (wNode c.p base w3) c.i w3.top.rootKey)
    (hwf : ∀ y yn, wNode c.p base w3 y = some yn → klongsWf yn.ks = true)
    (htm : ∀ y yn, wNode c.p base w3 y = some yn → ∀ s, Klong.time s ∈ yn.ks → s ≤ c.i)
    (hG3 : ∀ u un c' z, wNode c.p base w3 u = some un → (c', z) ∈ un.liveAt c.i → z < w3.next)
    (hfr3 : ∀ z, w3.next ≤ z → knodeOf c.p base z = none) :
    SplitStepOKW c base d' p q pn qn k1 w3 x := by
  intro w last _ _ _ _ _ _ hpk hsp hsc hf hs hfH hsH hT hqR hfree hlinks hL hpath hlook htk hnext
    htop hTw hRw hnone hlinkw
  obtain ⟨hX, hK, hS2, hlinkK, h0⟩ := id hP
  subst hXp hXq hNp hNq
  have hk1 : K (d' + 1) = k1 := by
    have := hK (d' + 1) (by omega) (Nat.le_refl _)
    rw [← hpath, hpk] at this
    simp only [Option.some.injEq, Prod.mk.injEq] at this
    exact this.1.symm
  subst hk1
  have hwX : ∀ i, i ≤ d' + 1 → wNode c.p base w3 (X i) = some (Nn i) := by
    intro i hi
    obtain ⟨a, b⟩ := hS2 i hi
    simp only [wNode, b, Bool.false_eq_true, ↓reduceIte, a]
  have hreach3 := pathOK_reach c base w3 (d' + 1) X K Nn hP
  have hdist := pathOK_dist c base w3 (d' + 1) X K Nn hP hT3
  have hsa2 : 2 ≤ c.p.splitAbove := by have := hmp.1; have := hmp.2.2.1; omega
  exact writerWP_handleFull_segSpaceChainV_live c base w3.path d' X K Nn last hX hK hlinkK
    (fun i h1 hi hNR hql' c' z hz hpos =>
      rangeG_of_rangeOrder c _ _ hRO htm _ _ _ _ _ (hreach3 (i - 1) (by omega)) (hwX (i - 1) (by omega))
        hql' (hlinkK i h1 (by omega)) (hwX i (by omega)) hNR c' z hz hpos)
    (fun i _ hi hNR hsp' => lenG_of_splitAbove c _ _ hsa2 _ _ (hreach3 i (by omega)) (hwX i (by omega))
      hNR hsp')
    (fun i hi => hwf _ _ (hwX i hi)) (fun i hi => htm _ _ (hwX i hi)) hdist hpnew hql hsp hsc hf hs
    hfH hsH hmp w hpath
    (fun i hi => ⟨by rw [hlook _ (hxX i hi) (hXlt i hi)]; exact (hS2 i hi).1,
      by rw [htk]; exact (hS2 i hi).2⟩)
    hTw (fun i hi => hRw _ (hreach3 i hi))
    (fun z hz => ⟨hnone z hz, (hfree z hz).2, hfr3 z (by omega)⟩)
    (fun u c' z hl => by
      rcases hlinkw u c' z hl with ⟨un, hun, hc⟩ | h
      · have := hG3 u un c' z hun hc; omega
      · omega)
    (by rw [htop]; exact h0.symm) hT hqR hlinks hL

/-- The merge's full parent p, not made by the transaction, a segment root split in
space below its segment leaf q (d ≥ 2), whatever q's room: its cascade
(`splitStepOKW_segChain`). -/
def MergeFullSpaceSegChain (c : Ctx) (v3 : W) (d : Nat) (p : NodeId) (pn xn ln rn : KNode)
    (il cL ir cR : Nat) : Prop :=
  pn.firstTime ≠ some c.i ∧
  (∀ last, mergeFullLast pn c.i cL v3.next cR (mergeM2 c xn ln rn cR v3.next) = some last →
    ¬ (pn.size + mergeParentNeed c.i pn il ir cR (mergeM2 c xn ln rn cR v3.next) ≤ c.p.M) ∧
      c.p.splitAbove < last.size) ∧
  2 ≤ d ∧ ∃ (q : NodeId) (qn : KNode) (k1 : Nat), (v3.path[d - 2]?).map (·.2) = some q ∧
    v3.path[d - 1]? = some (some k1, p) ∧ v3.nodes.lookup q = some qn ∧ qn.leaf = true

set_option maxHeartbeats 4000000 in
/-- The case `MergeFullSpaceSegChain` at a round with `MergeLiveOK`'s facts: the
merge's tail ends with the live counts, no hole. -/
theorem writerWP_mergeTail_liveSpaceChainRound (c : Ctx) (base : View BVal)
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
    (hN : MergeFullSpaceSegChain c v3 d p pn xn ln rn il cL ir cR) :
    WriterWP (mergeTail c x d p pn xn leftSome l ln il r rn ir) c w3
      (fun res v4 => (res = 1 → LiveHoleW key g (h + 1) c base v4) ∧
        (res ≠ 1 → LiveEdges c.p (wNode c.p base v4) c.i v4.top.rootKey)) := by
  obtain ⟨hpnew, hspace, hd2, q, qn, k1, hq3, hk3', hq3lk, hql⟩ := hN
  refine writerWP_mergeTail_liveSpaceRoundW c base hvc hm hMP key g h v v1 v3 d F w0 k0 KO X K Nn x p
    pn xn hS hd hr13 hk13 hp13 hLH hJ3 hP3 hx hpath hplk hpleaf hxlk leftSome l ln il r rn ir cL cR w3
    hr3 h3p hsrc3 hL hLL hR hRL hclt hadj hll hrl hxlr hln hrn hpre3 hpath3 hnB hpnew hspace hd2 q qn
    k1 hq3 hk3' hq3lk (fun _ _ _ => ?_)
  have hI : PutInv c base v3 := hJ3.1.1.1
  have hG : PutInvG c base v3 := hJ3.1.1.2.1
  have hRO : RangeOrder (wNode c.p base v3) c.i v3.top.rootKey := hJ3.1.1.2.2.1
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 2 := ⟨d - 2, by omega⟩
  have hd2' : d' + 2 - 2 = d' := by omega
  have hd1' : d' + 2 - 1 = d' + 1 := by omega
  rw [hd2'] at hq3 ⊢
  rw [hd1'] at hk3' hpath
  obtain ⟨hX, hK, hS2, hlinkK, h0⟩ := id hP3
  have hXi : ∀ i, i ≤ d' + 2 → ∀ z, (v3.path[i]?).map (·.2) = some z → z = X i := by
    intro i hi z hz; have := hX i hi; rw [hz] at this; exact Option.some.inj this
  have hpX := hXi (d' + 1) (by omega) p hpath
  have hqX := hXi d' (by omega) q hq3
  have hxX := hXi (d' + 2) (Nat.le_refl _) x hx
  have hqn : Nn d' = qn := by
    have := (hS2 d' (by omega)).1; rw [← hqX, hq3lk] at this; exact (Option.some.inj this).symm
  have hpnN : Nn (d' + 1) = pn := by
    have := (hS2 (d' + 1) (by omega)).1; rw [← hpX, hplk] at this; exact (Option.some.inj this).symm
  have hdist := pathOK_dist c base v3 (d' + 2) X K Nn hP3 hI.tree
  have hN3 : wNode c.p base w3 = wNode c.p base v3 := hr3.1
  have hnx : w3.next = v3.next := hr3.2.2.2.2
  refine splitStepOKW_segChain c base hMP d' p q pn qn k1 w3 x X K Nn
    ⟨fun i hi => by rw [hpath3]; exact hX i (by omega),
      fun i h1 hi => by rw [hpath3]; exact hK i h1 (by omega),
      fun i hi => ⟨lookup_of_prefix _ _ hpre3 _ _ (hS2 i (by omega)).1,
        by rw [hr3.2.2.1]; exact (hS2 i (by omega)).2⟩,
      fun i h1 hi => hlinkK i h1 (by omega), by rw [h0, hr3.2.1]⟩
    hpX.symm hqX.symm hpnN hqn hpnew hql
    (fun i hi he => by rw [hxX] at he; have := hdist i (d' + 2) (by omega) (Nat.le_refl _) he; omega)
    (fun i hi => by
      rw [hnx]; exact hI.ids.1 (X i) (by rw [(hS2 i (by omega)).1]; rfl))
    (by rw [hN3, hr3.2.1]; exact hI.tree) (by rw [hN3, hr3.2.1]; exact hRO)
    (by rw [hN3]; exact hI.wf) (by rw [hN3]; exact hI.times)
    (by rw [hN3, hnx]; exact hG.links)
    (fun z hz => (hI.fresh z (by rw [← hnx]; exact hz)).1)

/-! ## What is left of `MergeTailFullRest6OK` -/

/-- `MergeTailFullRest6OK` but in its case `MergeFullSpaceSegChain` (bergdb 030-01,
step 3's rest): the merge's tail where its parent p goes `full`, and p, not made by
the transaction, is the space root (d = 1) split in space, or split in time with a
merge into two nodes, or p is not a segment root and q has no room for p's new
klongs or would compact (the cascade below an inner parent), or q has none for
p's copy's klong (a time split's cascade); or p, made by the transaction, splits in
space (in place). -/
def MergeTailFullRest7OK (c : Ctx) (base : View BVal) (B : NodeId) (H : NodeId → Nat → Prop) :
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
    WriterWP (mergeTail c x d p pn xn leftSome l ln il r rn ir) c w3
      (fun res v4 => (res = 1 → LiveHoleW key g (h + 1) c base v4) ∧
        (res ≠ 1 → LiveEdges c.p (wNode c.p base v4) c.i v4.top.rootKey))

/-- `MergeTailFullRest6OK` from its rest: its case `MergeFullSpaceSegChain` (a segment
root split in space below its segment leaf, the cascade included) is proved
(`writerWP_mergeTail_liveSpaceChainRound`). -/
theorem mergeTailFullRest6OK_of_rest7 (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (hm : c.p.merges = true) (hMP : MergeParamsOK c.p) {B : NodeId} {H : NodeId → Nat → Prop}
    (hvo : ViewHtOK H B c) (hF : MergeTailFullRest7OK c base B H) :
    MergeTailFullRest6OK c base B H := by
  intro key g h v v1 v3 d F w0 k0 KO top0 X K Nn x p pn xn hS hd hr13 hk13 hp13 hLH hJ3 hpb3 hP3 hb1
    hi1 hpf1 hi3 hx hpath hplk hpleaf hxlk hcnt leftSome l ln il r rn ir cL cR w3 hr3 h3p hk3 hsrc3
    hL hLL hR hRL hclt hadj hll hrl hxlr hln hrn hpre3 hpath3 hnB hNT hNM hNS hNG hNSG hNR
  by_cases hN : MergeFullSpaceSegChain c v3 d p pn xn ln rn il cL ir cR
  · exact writerWP_mergeTail_liveSpaceChainRound c base hvc hm hMP key g h v v1 v3 d F w0 k0 KO X K Nn
      x p pn xn hS hd hr13 hk13 hp13 hLH hJ3 hP3 hx hpath hplk hpleaf hxlk leftSome l ln il r rn ir cL
      cR w3 hr3 h3p hsrc3 hL hLL hR hRL hclt hadj hll hrl hxlr hln hrn hpre3 hpath3 hnB hN
  · exact hF key g h v v1 v3 d F w0 k0 KO top0 X K Nn x p pn xn hS hd hr13 hk13 hp13 hLH hJ3 hpb3 hP3
      hb1 hi1 hpf1 hi3 hx hpath hplk hpleaf hxlk hcnt leftSome l ln il r rn ir cL cR w3 hr3 h3p hk3
      hsrc3 hL hLL hR hRL hclt hadj hll hrl hxlr hln hrn hpre3 hpath3 hnB hNT hNM hNS hNG hNSG hNR hN

/-- `afterDelete` with the hole (bergdb 030-01, steps 3 and 4): from the call's
facts to `LiveEdges`, premises `MergeTailFullRest7OK`, `MergeParamsOK` and R3
after the merges' loop. -/
theorem writerWP_afterDelete_liveTR7 (key : Key) (g : Nat) (c : Ctx) (base : View BVal)
    (hvc : ViewCoherent c base) (hm : c.p.merges = true) (hMP : MergeParamsOK c.p) (KO : KindOracle)
    (B : NodeId) (hv : ViewIdsBelow B c.view) (hk : ViewKinds KO B c)
    (hICEk : ICEFromKinds c base KO B) (hsa2 : 2 ≤ c.p.splitAbove) (hcap : 1 ≤ c.p.mergeMax)
    (hpos : 0 < c.i) {H : NodeId → Nat → Prop} (hvo : ViewHtOK H B c)
    (hkw : ViewKlongsWf c.p c.view) (top0 : Top) (hB : PutBase c base B)
    (hF : MergeTailFullRest7OK c base B H)
    (v : W) (hJ : DelInvJAE c base KO B B v) (hpb : PutBook c B top0 v) (hhi : HtInv H B c v)
    (hLH : LiveHoleW key g 0 c base v)
    (hR3 : WriterWP (mergeUp key g c.p.fuel 0 false) c v
      (fun merged v' => merged = true → R3At key g c v')) :
    WriterWP (afterDelete key g 0) c v
      (fun _ v' => LiveEdges c.p (wNode c.p base v') c.i v'.top.rootKey) :=
  writerWP_afterDelete_liveTR6 key g c base hvc hm hMP KO B hv hk hICEk hsa2 hcap hpos hvo hkw top0 hB
    (mergeTailFullRest6OK_of_rest7 c base hvc hm hMP hvo hF) v hJ hpb hhi hLH hR3

end SIS.Tree
