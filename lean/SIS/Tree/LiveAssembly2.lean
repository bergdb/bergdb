/-
`l4` assembled, continued (bergdb 030-01, steps 5 and 7): R4 narrowed and l4c's
latest merge tail. The full leaf split in time below a parent without room has
its copy filled (`ChildOK` at the copy: no hole, the cascade by
`writerWP_appendKlongs_chainGL`, `liveDel_fullTimeChainF`) or a hole below an
inner parent (`DelFullTimeHoleM`, what is left of R4). `invGetScanOK_merges_noL4c`
takes that and l4c's `MergeTailFullRest6OK`. Like its predecessors it has
`R3Calls`, believed false at unreached states (030-01's log, 2026-11-17, 01:56).
-/
import SIS.Tree.LiveAssembly
import SIS.Tree.LiveMergeRoot

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- The live counts with one hole L, not the space root, whose every link meets
`ChildOK`: the live counts. -/
theorem liveEdges_of_holeChild (p : Params) (N : NodeId → Option KNode) (t : Time) (r L : NodeId)
    (h : LiveEdgesH p N t r (fun z => z = L)) (hLr : L ≠ r)
    (hc : ∀ u un c yn, TReach N t r u → N u = some un → (c, L) ∈ un.liveAt t → N L = some yn →
      ChildOK p t un yn) :
    LiveEdges p N t r := by
  refine ⟨fun rn hrn => ⟨(h.1 rn hrn).1, (h.1 rn hrn).2 (fun he => hLr he.symm)⟩,
    fun u un c y yn hu hun hcy hyn => ?_⟩
  by_cases hy : y = L
  · subst hy; exact hc u un c yn hu hun hcy hyn
  · exact (h.2 u un c y yn hu hun hcy hyn).1 hy

set_option maxHeartbeats 8000000 in
/-- A full leaf X (D + 1) that the transaction did not make, split in time with a
last version given (a delete's), its copy filled under X D (`hfill`), and the
cascade (`writerWP_appendKlongs_chainGL`'s premises for X 0 .. X D): from the live
counts at the start, with the last version's live klongs the leaf's, they hold
after, with no hole. -/
theorem writerWP_handleFull_timeChain_live (c : Ctx) (base : View BVal)
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
    (hfirst : (Nn (D + 1)).firstTime ≠ some c.i) (hnl : (Nn (D + 1)).leaf = true)
    (hcs : (!compact && decide (last.size > c.p.splitAbove)) = false)
    (hsub : ∀ c' z, (c', z) ∈ (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode).liveAt c.i →
      (c', z) ∈ (Nn (D + 1)).liveAt c.i)
    (hpos : (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode).liveAt c.i ≠ [])
    (hfill : (Nn D).leaf = false → c.p.merges = true →
      c.p.mergeBelow ≤ ((⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode).liveAt c.i).length)
    (hmp : MergeParamsOK c.p)
    (w : W) (hS1 : w.path = path0)
    (hS2 : ∀ i, i ≤ D + 1 → w.nodes.lookup (X i) = some (Nn i) ∧ w.taken.contains (X i) = false)
    (hS3 : TreeOK (wNode c.p base w) c.i w.top.rootKey)
    (hS4 : ∀ i, i ≤ D + 1 → TReach (wNode c.p base w) c.i w.top.rootKey (X i))
    (hS5 : ∀ z, w.next ≤ z → w.nodes.lookup z = none ∧ w.taken.contains z = false ∧
      knodeOf c.p base z = none)
    (hS6 : ∀ u c' z, TLink (wNode c.p base w) c.i u c' z → z < w.next)
    (hR0 : w.top.rootKey = X 0)
    (hL : LiveEdges c.p (wNode c.p base w) c.i w.top.rootKey) :
    WriterWP (handleFullWith (fun q more => appendKlongs D q more) (D + 1) (X (D + 1)) [] last
      compact) c w (fun _ w' => LiveEdges c.p (wNode c.p base w') c.i w'.top.rootKey) := by
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
  -- the tree with the leaf's node its last version: the live counts, the copy filled
  have hTu : TreeOK (updN (wNode c.p base w) (X (D + 1)) (Nn (D + 1))) c.i w.top.rootKey := by
    rw [updN_self_eq _ _ _ hwx]; exact hS3
  obtain ⟨hTV, hRV⟩ := treeOK_updN_sub _ c.i _ _ (Nn (D + 1)) ⟨(Nn (D + 1)).leaf, last.ks⟩ hTu hsub
  rw [updN_self_eq _ _ _ hwx] at hRV
  have hLVH := liveEdgesH_leaf_shrink c.p (wNode c.p base w) c.i w.top.rootKey (X (D + 1)) (Nn (D + 1))
    ⟨(Nn (D + 1)).leaf, last.ks⟩ hL hwx hnl hnl (fun q hq => hsub q.1 q.2 hq) hpos
  have hLV0 : LiveEdges c.p (updN (wNode c.p base w) (X (D + 1)) ⟨(Nn (D + 1)).leaf, last.ks⟩) c.i
      w.top.rootKey := by
    refine liveEdges_of_holeChild c.p _ c.i _ _ hLVH hXr ?_
    intro u un cc yn hu hun hcu hyn
    rw [updN_self] at hyn
    simp only [Option.some.injEq] at hyn
    subst hyn
    have hu0 := hRV u hu
    have hux : u ≠ X (D + 1) := by
      intro he
      rw [he, updN_self] at hun
      simp only [Option.some.injEq] at hun
      subst hun
      exact hS3.no_self_link (X (D + 1)) cc (hS4 (D + 1) (Nat.le_refl _))
        ⟨_, hwx, hsub _ _ hcu⟩
    rw [updN_ne _ _ _ _ hux] at hun
    obtain ⟨he, _⟩ := hS3.oneLink u cc (X D) (K (D + 1)) (X (D + 1)) hu0 (hS4 D (by omega))
      ⟨un, hun, hcu⟩ ⟨Nn D, hwq, hkl⟩
    subst he
    rw [hwq] at hun
    simp only [Option.some.injEq] at hun
    subst hun
    refine ⟨hpos, fun _ hl => ?_, fun hql hm => hfill hql hm⟩
    simp only [hnl] at hl; cases hl
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
  have hfreshV : ∀ u c', TReach (updN (wNode c.p base w) (X (D + 1)) ⟨(Nn (D + 1)).leaf, last.ks⟩) c.i
      w.top.rootKey u → ¬ TLink (updN (wNode c.p base w) (X (D + 1)) ⟨(Nn (D + 1)).leaf, last.ks⟩) c.i
        u c' w.next := by
    intro u c' _ hl
    obtain ⟨m, hm, hc⟩ := hl
    by_cases hux : u = X (D + 1)
    · rw [hux, updN_self] at hm
      simp only [Option.some.injEq] at hm
      subst hm
      have := hS6 _ c' w.next ⟨_, hwx, hsub _ _ hc⟩; omega
    · rw [updN_ne _ _ _ _ hux] at hm
      have := hS6 u c' w.next ⟨m, hm, hc⟩; omega
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
        have := hS6 _ c' z ⟨_, hwx, hsub _ _ hc⟩; omega
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
      LiveEdges c.p (wNode c.p base w3) c.i w3.top.rootKey := by
    intro w3 h3n h3t h3top
    have hN3 := wNode_upsert_updN c.p base w2 w3 (X (D + 1)) _ h3n h3t htk2
    have hxR2 : ¬ TReach (wNode c.p base w2) c.i w2.top.rootKey (X (D + 1)) := by
      intro h
      rcases h2reach _ h with h' | h'
      · rw [h1top] at h'
        exact (hR1V _ h').2 rfl
      · have := hXlt (D + 1) (Nat.le_refl _); omega
    have hLV' := (liveEdgesX_false_iff _ _ _ _).mp hLV
    rw [← h1top] at hLV'
    rw [hN3, h3top]
    exact liveEdges_updN_unreach _ _ _ _ _ _ hxR2 (h2live hmp hLV')
  exact key _ rfl rfl rfl

/-! ## The case: the full leaf split in time with its cascade, the copy filled -/

/-- A delete, the merges on, whose leaf keeps a live klong and is full, split in
time (`DelFullTimeGM`'s path), not made by the transaction, below the space root,
its copy (the last version without the key) filled under its parent: m live
klongs or more if the parent is inner. No room is asked of the parent. -/
def DelFullTimeChainFM (c : Ctx) (base : View BVal) (w : W) (op : Op) : Prop :=
  ∃ pre cv L n, op = .del (pre ++ [cv]) ∧ c.p.merges = true ∧ KeyLeaf c base w pre cv L n ∧
    bitsUnion n.lastBitmap (n.bitsOf cv) ≠ n.lastBitmap ∧
    n.allKeysIn (bitsUnion n.lastBitmap (n.bitsOf cv)) = false ∧ ¬ DelRoom c cv n ∧
    ((n.lastVersionGivenDel c.i (bitsUnion n.lastBitmap (n.bitsOf cv))).size ≤ c.p.splitAbove ∨
      ((∃ old, n.ks.getLast? = some (.del old)) ∧ n.lastTime = some c.i) ∨ n.size + 1 < c.p.M) ∧
    n.firstTime ≠ some c.i ∧ L ≠ w.top.rootKey ∧
    ∀ q qn k1, TReach (wNode c.p base w) c.i w.top.rootKey q → wNode c.p base w q = some qn →
      (k1, L) ∈ qn.liveAt c.i → qn.leaf = false →
      c.p.mergeBelow ≤ ((n.lastVersionGivenDel c.i (bitsUnion n.lastBitmap (n.bitsOf cv))).liveAt c.i).length

set_option maxHeartbeats 4000000 in
/-- The full leaf not made by the transaction, split in time with its cascade, its
copy filled, calls `afterDelete` with the live counts (no hole), in the
stratum (bergdb 030-01, step 5): any `afterDelete` that keeps the live counts from
the hole at (g, 0) gives them after. -/
theorem liveDel_fullTimeChainF (p : Params) (R : Struct BVal → Time → Prop) (hM : 2 ≤ p.M)
    (hsa2 : 2 ≤ p.splitAbove) (hp : MergeParamsOK p)
    (hRL : ∀ P t, R P t → RunLinksOK p P t)
    (hRP : ∀ P t, R P t → PointersOK P) (hRK : ∀ P t, R P t → KindsAllOK p P) :
    ∀ ts tx, Within p (ts ++ [tx]) → R (treeRun p ts) ts.length → ∀ z top,
      lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z →
      topOf p (ctxOf p ts).view z = .ok top →
      ∀ pre op post, tx.ops = pre ++ op :: post →
      ∀ r w, (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
      SJ0 p ts tx w → TakeJ2 (ctxOf p ts) (viewOf (treeRun p ts)) tx.base w →
      ∀ key, op = .del key → DelFullTimeChainFM (ctxOf p ts) (viewOf (treeRun p ts)) w op →
      ∀ Q : W → Prop, (∀ v, Q v → WriterWP fresh (ctxOf p ts) v (fun _ v' => Q v')) →
      (∀ g v, DelInvJT (ctxOf p ts) (viewOf (treeRun p ts)) (kindOracleOf p (treeRun p ts))
          tx.base tx.base v → PutBook (ctxOf p ts) tx.base top v →
        HtInv (htOracleOf p (treeRun p ts)) tx.base (ctxOf p ts) v →
        LiveHoleW key g 0 (ctxOf p ts) (viewOf (treeRun p ts)) v →
        WriterWP (afterDelete key g 0) (ctxOf p ts) v (fun _ v' => Q v')) →
      WriterWP (putKv op) (ctxOf p ts) w (fun _ w' => Q w') := by
  intro ts tx hw hr z top _ htop ops op post hops r w hpre hS hJ key hop hPc Q hfresh hA
  obtain ⟨pre, cv, L0, n0, hop', _, hK, hne0, hkeep0, hfull0, hsz0, hnm0, hnr0, hpar0⟩ := hPc
  subst hop'
  cases hop
  have hI : PutInv (ctxOf p ts) (viewOf (treeRun p ts)) w := hS.1.1.1.1.1
  have hRO : RangeOrder (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey := hS.1.1.2
  have hSB : tx.base ≤ w.next := hS.1.1.1.2
  have hLC0 : LiveCounts p (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey := hS.2.2
  have hkey : keyWf (pre ++ [cv]) = true := within_op_keyWf p ts tx hw ops _ post hops
  obtain ⟨rk, hrk, _⟩ := keyLeaf_rk hK
  have hB := putBase_of_run p ts tx hw (hRL _ _ hr)
  have hbook := putBook_reached p ts tx hw (hRL _ _ hr) z top htop ops r w hpre
  have hG := putInvG_of_book _ _ tx.base top w hB hbook
  have hLV := leafVals_all hS.1.1.1.1.2 hkey hrk
  have hpos : 0 < (ctxOf p ts).i := by simp [ctxOf]
  obtain ⟨hv, hk, hb0, hi0⟩ := kd_contextR p hM ts tx (hRP _ _ hr) (hRK _ _ hr) hw top ops (.del (pre ++ [cv]) :: post) hops r w hpre
  have hICEk : ICEFromKinds (ctxOf p ts) (viewOf (treeRun p ts)) (kindOracleOf p (treeRun p ts)) tx.base :=
    fun v hb hi hun => innerChildren_of_kinds p (treeRun p ts) tx.base (ctxOf p ts) v rfl (hRK _ _ hr)
      (hRP _ _ hr) hb hi.cache hun
  have hJ0 : KdJ (ctxOf p ts) tx.base top (kindOracleOf p (treeRun p ts)) tx.base w := ⟨hbook, hb0, hi0⟩
  obtain ⟨hvo, hkw, _, _, hbw, hiw, hwfw0⟩ := hS.2.1
  refine writerWP_del_toLeafMKH (ctxOf p ts) _ (viewCoherent_ctxOf p ts) pre cv rk w
    (fun v => KdJ (ctxOf p ts) tx.base top (kindOracleOf p (treeRun p ts)) tx.base v ∧
      HtJ0 (ctxOf p ts) (htOracleOf p (treeRun p ts)) tx.base v)
    (fun s f x v hJ hx => writerWP_and (kdJ_descendLte _ _ tx.base top hB _ tx.base hv hk s f x v hJ.1 hx)
      (htJ0_descendLte hvo hkw s f x v hJ.2 hx))
    (fun s fd L n v hJ hL hlk hleaf hfd =>
      ⟨kdJ_pathAdd _ _ tx.base top hB _ tx.base hv fd.c fd.y L n v hJ.1 hL hlk
        (kd_searchEq_mem n _ s fd hfd), htJ0_pathAdd hvo s fd L n v hJ.2 hL hlk hleaf hfd⟩)
    ⟨kdJ_start _ _ tx.base top hB _ tx.base hv w hJ0, htJ0_start hvo w hbw hiw hwfw0⟩
    hrk (hI.pathUntaken _) hI.wf _ hfresh ?_
  intro L n P w3 hL hn hnl hr03 hJ3h hlk3 hp3' hlinkP hXD hlkX
  have hJ3 := hJ3h.1
  have hH3 := hJ3h.2
  obtain ⟨g0, h0, hm0⟩ := kd_tag_of_lookup hH3.book hlk3
  obtain ⟨hne, hkeep, hfull, hsz, hnm, hnr, hpar⟩ := keyLeaf_all2 hK hrk
    (fun L' m => bitsUnion m.lastBitmap (m.bitsOf cv) ≠ m.lastBitmap ∧
      m.allKeysIn (bitsUnion m.lastBitmap (m.bitsOf cv)) = false ∧ ¬ DelRoom (ctxOf p ts) cv m ∧
      ((m.lastVersionGivenDel (ctxOf p ts).i (bitsUnion m.lastBitmap (m.bitsOf cv))).size ≤
        (ctxOf p ts).p.splitAbove ∨ ((∃ old, m.ks.getLast? = some (.del old)) ∧
        m.lastTime = some (ctxOf p ts).i) ∨ m.size + 1 < (ctxOf p ts).p.M) ∧
      m.firstTime ≠ some (ctxOf p ts).i ∧ L' ≠ w.top.rootKey ∧
      ∀ q qn k1, TReach (wNode (ctxOf p ts).p (viewOf (treeRun p ts)) w) (ctxOf p ts).i w.top.rootKey q →
        wNode (ctxOf p ts).p (viewOf (treeRun p ts)) w q = some qn →
        (k1, L') ∈ qn.liveAt (ctxOf p ts).i → qn.leaf = false →
        (ctxOf p ts).p.mergeBelow ≤ ((m.lastVersionGivenDel (ctxOf p ts).i
          (bitsUnion m.lastBitmap (m.bitsOf cv))).liveAt (ctxOf p ts).i).length)
    ⟨hne0, hkeep0, hfull0, hsz0, hnm0, hnr0, hpar0⟩ L n hL hn hnl
  have hLt : w.taken.contains L = false :=
    hI.pathUntaken _ (L, cv) (fromVisits_append _ _ _ pre cv _ rk hrk _ hL)
  have h3t : w3.taken.contains L = false := by rw [hr03.2.2.1]; exact hLt
  obtain ⟨a, hpx⟩ := path_last_of_toLeaf w w3 P L hp3' hXD
  have hPOK := pathOK_of_toLeaf (ctxOf p ts) _ w w3 P n hI hr03 hp3' hlinkP hlkX
  have hJ3' : TakeJ2 (ctxOf p ts) (viewOf (treeRun p ts)) tx.base w3 := takeJ2_of_readsAs _ _ _ w w3 hJ hr03
  have hJ2 := writerWP_appendDeleteKlong_full_j2_any (ctxOf p ts) _ tx.base hpos
    (delFullRootJ2OK_ctx p hsa2 ts tx.base) w3
    (putInv_of_readsAs _ _ w w3 hI hr03) (putInvG_of_readsAs _ _ w w3 hG hr03)
    (by rw [hr03.1, hr03.2.1]; exact hRO) hJ3' (by rw [hr03.2.2.2.2]; exact hSB) hsa2
    P.length _ _ _ hPOK cv n (by show (wNode _ _ w (nodeAt w.top.rootKey P P.length)).getD _ = n; rw [hXD, hn]; rfl)
    hnl hne hfull (fun y hy => by rw [hr03.1]; exact (hLV L n hL hn hnl y hy).1)
  simp only [hXD] at hJ2
  -- the path: L below its parent q
  have hPpos : 0 < P.length := by
    cases hPe : P with
    | nil => rw [hPe] at hXD; simp [nodeAt] at hXD; exact absurd hXD.symm hnr
    | cons _ _ => simp
  obtain ⟨d', hd'⟩ : ∃ d', P.length = d' + 1 := ⟨P.length - 1, by omega⟩
  obtain ⟨kq, qm, hPq, hqm, hkq⟩ := LinkedFrom.get _ _ _ P hlinkP d' (by omega)
  rw [← hd', hXD] at hPq hkq
  have hqR : TReach (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey (nodeAt w.top.rootKey P d') :=
    (LinkedFrom.pathLen _ _ _ P hlinkP d' (by omega)).reach
  have hfillq := hpar _ qm kq hqR hqm hkq
  have hI3 := putInv_of_readsAs _ _ w w3 hI hr03
  -- the halves
  generalize hlast : n.lastVersionGivenDel (ctxOf p ts).i (bitsUnion n.lastBitmap (n.bitsOf cv)) = last
    at hfillq
  have hlastl : last.leaf = n.leaf := by rw [← hlast]; rfl
  have hlastN : (⟨n.leaf, last.ks⟩ : KNode) = last := by rw [← hlastl]
  have hlive' : ∀ c', last.live.lookup c' = if c' == cv then none else n.live.lookup c' := by
    intro c'; rw [← hlast]; exact KNode.delete_live_lookup n _ cv c'
  have htl : ∀ s, Klong.time s ∈ last.ks → s ≤ (ctxOf p ts).i := by
    intro s hs
    rw [← hlast] at hs
    simp only [KNode.lastVersionGivenDel, List.mem_cons, List.mem_map] at hs
    rcases hs with he | ⟨_, _, he⟩
    · cases he; exact Nat.le_refl _
    · cases he
  have htn := hI.times L n hn
  obtain ⟨hsubl, _⟩ := live_shrink n last cv hlive'
  have hsub : ∀ q ∈ last.liveAt (ts.length + 1), q ∈ n.liveAt (ts.length + 1) := by
    rw [KNode.liveAt_of_times n (ts.length + 1) htn, KNode.liveAt_of_times last (ts.length + 1) htl]; exact hsubl
  have hposl : last.liveAt (ts.length + 1) ≠ [] := by
    rw [KNode.liveAt_of_times last (ts.length + 1) htl]; exact live_ne_of_keep n last cv hkeep hlive'
  -- names
  generalize hqdef : nodeAt w.top.rootKey P d' = q at hqm hkq hqR hPq
  have hqL : q ≠ L := by
    intro he
    rw [← hqdef, ← hXD] at he
    have := PathLen.depth_unique hI.tree _ _ _ (LinkedFrom.pathLen _ _ _ P hlinkP d' (by omega))
      (by rw [he]; exact LinkedFrom.pathLen _ _ _ P hlinkP P.length (Nat.le_refl _))
    omega
  have hqt : w.taken.contains q = false := hI.untaken q (tReach_reachS _ _ _ _ hqR)
  have hlq3 : w3.nodes.lookup q = some qm := by
    have := hlkX d' (by omega)
    rw [hqdef, hqm] at this
    exact this
  have hnext3 : w3.next = w.next := hr03.2.2.2.2
  have hNw3 : wNode p (viewOf (treeRun p ts)) w3 = wNode p (viewOf (treeRun p ts)) w := hr03.1
  have hwfree : ∀ z, w.next ≤ z → wNode p (viewOf (treeRun p ts)) w z = none ∧
      w.taken.contains z = false := by
    intro z hz
    have hl : w.nodes.lookup z = none := by
      cases h' : w.nodes.lookup z with
      | none => rfl
      | some m => have := hI.ids.1 z (by rw [h']; rfl); omega
    have ht : w.taken.contains z = false := by
      cases h' : w.taken.contains z with
      | false => rfl
      | true => have := hI.ids.2.2.1 z h'; omega
    refine ⟨?_, ht⟩
    simp only [wNode, ht, Bool.false_eq_true, ↓reduceIte, hl]
    exact (hI.fresh z hz).1
  -- the split's live part
  have hlive : WriterWP (appendDeleteKlong L P.length cv) (ctxOf p ts) w3 (fun _ v =>
      LiveEdges p (wNode p (viewOf (treeRun p ts)) v) (ts.length + 1) v.top.rootKey) := by
    refine writerWP_appendDeleteKlong_full_ofP L P.length cv n _ w3 hlk3 hne hfull _ ?_
    intro compact s hpath
    have hcs : (!compact && decide (last.size > (ctxOf p ts).p.splitAbove)) = false := by
      rw [← hlast]; exact compact_time_of_path n (ctxOf p ts) cv compact hsz hpath
    generalize hw4 : ({ w3 with trail := s :: w3.trail } : W) = w4
    have h4n : w4.nodes = w3.nodes := by rw [← hw4]
    have h4t : w4.taken = w3.taken := by rw [← hw4]
    have h4top : w4.top = w3.top := by rw [← hw4]
    have h4next : w4.next = w3.next := by rw [← hw4]
    have hN4 : wNode (ctxOf p ts).p (viewOf (treeRun p ts)) w4 = wNode p (viewOf (treeRun p ts)) w := by
      rw [← hNw3]; unfold wNode; rw [h4n, h4t]; rfl
    have hroot4 : w4.top.rootKey = w.top.rootKey := by rw [h4top, hr03.2.1]
    have hw4n : w4.next = w.next := by rw [h4next, hnext3]
    have hPOK4 : PathOK (ctxOf p ts) w4 P.length (fun i => nodeAt w.top.rootKey P i)
        (fun i => ((P[i - 1]?).bind (·.1)).getD 0)
        (fun i => (wNode (ctxOf p ts).p (viewOf (treeRun p ts)) w (nodeAt w.top.rootKey P i)).getD
          ⟨true, []⟩) := by
      rw [← hw4]; exact hPOK
    rw [hd'] at hPOK4
    have hT4 : TreeOK (wNode (ctxOf p ts).p (viewOf (treeRun p ts)) w4) (ctxOf p ts).i w4.top.rootKey := by
      rw [hN4, hroot4]; exact hI.tree
    have hreach4 := pathOK_reach (ctxOf p ts) (viewOf (treeRun p ts)) w4 (d' + 1) _ _ _ hPOK4
    have hdist4 := pathOK_dist (ctxOf p ts) (viewOf (treeRun p ts)) w4 (d' + 1) _ _ _ hPOK4 hT4
    obtain ⟨hX4, hK4, hS24, hlink4, h04⟩ := hPOK4
    have hw4X : ∀ j, j ≤ d' + 1 → wNode (ctxOf p ts).p (viewOf (treeRun p ts)) w4 (nodeAt w.top.rootKey P j) =
        some ((wNode (ctxOf p ts).p (viewOf (treeRun p ts)) w (nodeAt w.top.rootKey P j)).getD ⟨true, []⟩) := by
      intro j hj
      obtain ⟨a, b⟩ := hS24 j hj
      simp only [wNode, b, Bool.false_eq_true, ↓reduceIte, a]
    have hRO4 : RangeOrder (wNode (ctxOf p ts).p (viewOf (treeRun p ts)) w4) (ctxOf p ts).i w4.top.rootKey := by
      rw [hN4, hroot4]; exact hRO
    have htm4 : ∀ x xn, wNode (ctxOf p ts).p (viewOf (treeRun p ts)) w4 x = some xn →
        ∀ s, Klong.time s ∈ xn.ks → s ≤ (ctxOf p ts).i := by
      rw [hN4]; exact hI.times
    have hwf4 : ∀ x xn, wNode (ctxOf p ts).p (viewOf (treeRun p ts)) w4 x = some xn →
        klongsWf xn.ks = true := by
      rw [hN4]; exact hI.wf
    have hNnD1 : (wNode (ctxOf p ts).p (viewOf (treeRun p ts)) w (nodeAt w.top.rootKey P (d' + 1))).getD
        ⟨true, []⟩ = n := by
      rw [← hd', hXD]
      show (wNode p (viewOf (treeRun p ts)) w L).getD _ = n
      rw [show wNode p (viewOf (treeRun p ts)) w L = some n from hn]; rfl
    have hNnD : (wNode (ctxOf p ts).p (viewOf (treeRun p ts)) w (nodeAt w.top.rootKey P d')).getD
        ⟨true, []⟩ = qm := by
      rw [hqdef]
      show (wNode p (viewOf (treeRun p ts)) w q).getD _ = qm
      rw [show wNode p (viewOf (treeRun p ts)) w q = some qm from hqm]; rfl
    rw [hlast]
    rw [← hXD]
    unfold handleFull
    rw [hd']
    have hmain := writerWP_handleFull_timeChain_live (ctxOf p ts) (viewOf (treeRun p ts)) w4.path d'
      (fun i => nodeAt w.top.rootKey P i) (fun i => ((P[i - 1]?).bind (·.1)).getD 0)
      (fun i => (wNode (ctxOf p ts).p (viewOf (treeRun p ts)) w (nodeAt w.top.rootKey P i)).getD ⟨true, []⟩)
      last compact hX4 hK4 hlink4
      (fun i h1 hi hNR hql' c' z hz hpos' =>
        rangeG_of_rangeOrder (ctxOf p ts) _ _ hRO4 htm4 _ _ _ _ _
          (hreach4 (i - 1) (by omega)) (hw4X (i - 1) (by omega)) hql' (hlink4 i h1 (by omega))
          (hw4X i (by omega)) hNR c' z hz hpos')
      (fun i _ hi hNR hsp' => lenG_of_splitAbove (ctxOf p ts) _ _ hsa2 _ _ (hreach4 i (by omega))
        (hw4X i (by omega)) hNR hsp')
      (fun i hi => hwf4 _ _ (hw4X i hi)) (fun i hi => htm4 _ _ (hw4X i hi))
      (fun i i' hi hi' he => hdist4 i i' hi hi' he)
      (by (try simp only []); rw [hNnD1]; exact hnm) (by (try simp only []); rw [hNnD1]; exact hnl) hcs
      (by
        (try simp only []); rw [hNnD1]
        intro c' z' h
        exact hsub _ (by rw [← hlastN]; exact h))
      (by (try simp only []); rw [hNnD1, hlastN]; exact hposl)
      (by
        (try simp only []); rw [hNnD, hNnD1, hlastN]
        intro hql _
        exact hfillq hql)
      hp w4 rfl hS24 hT4 hreach4
      (by
        intro z hz
        rw [hw4n] at hz
        have hl : w3.nodes.lookup z = none := by
          cases h' : w3.nodes.lookup z with
          | none => rfl
          | some m => have := hI3.ids.1 z (by rw [h']; rfl); omega
        have ht : w3.taken.contains z = false := by
          cases h' : w3.taken.contains z with
          | false => rfl
          | true => have := hI3.ids.2.2.1 z h'; omega
        exact ⟨by rw [h4n]; exact hl, by rw [h4t]; exact ht, (hI3.fresh z (by rw [hnext3]; exact hz)).1⟩)
      (by
        rw [hN4, hw4n]
        intro u c' z' hl
        obtain ⟨un, hun, hc⟩ := hl
        exact hG.links u un c' z' hun hc)
      h04.symm
      (by rw [hN4, hroot4]; exact edges_of_liveCounts p _ _ _ hLC0)
    exact hmain
  refine writerWP_deleteUpward_gh (ctxOf p ts) L n P.length cv (pre ++ [cv]) w3 hlk3 hne hkeep
    (fun v => DelInvJT (ctxOf p ts) (viewOf (treeRun p ts)) (kindOracleOf p (treeRun p ts)) tx.base tx.base v ∧
      PutBook (ctxOf p ts) tx.base top v ∧
      HtInv (htOracleOf p (treeRun p ts)) tx.base (ctxOf p ts) v ∧
      LiveEdges p (wNode p (viewOf (treeRun p ts)) v) (ts.length + 1) v.top.rootKey)
    _ ?_ ?_
  · refine writerWP_mono (writerWP_and (writerWP_and (writerWP_and (writerWP_and
      (writerWP_appendDeleteKlong_full_delT (ctxOf p ts) _ (viewCoherent_ctxOf p ts)
        _ tx.base (delFullRootStepOKT_ctx p ts) hsa2 hv hk hICEk w pre cv rk tx.base top hB hI hRO
        hkey hrk L n P w3 hL hn hnl hne hfull hr03 hJ3 hp3' hlinkP hXD hlkX) hJ2)
      (putBook_appendDeleteKlong L _ cv _ _ tx.base top hB _ hJ3.1))
      (ht_appendDeleteKlong tx.base L P.length cv _ w3 hvo hpos hH3.book hH3.inv g0 h0 hm0 a hpx
        (hH3.free.mono (by rw [hp3']; simp)))) hlive) ?_
    rintro _ v ⟨⟨⟨⟨hDT, hJv⟩, hpbv⟩, ⟨_, hhiv, _, _⟩⟩, hE⟩
    exact ⟨⟨hDT, hJv⟩, hpbv, hhiv, hE⟩
  · intro g h v hgh ⟨hD, hpbv, hhiv, hE⟩
    have hh0 : h = 0 := kd_h0 hH3.book hlk3 (bk_mem_of_lookup _ _ _ hgh) hnl
    subst hh0
    exact hA g v hD hpbv hhiv (liveEdgesH_of_liveEdges _ _ _ _ _ hE)

/-- The full leaf not made by the transaction, split in time with its cascade, its
copy filled, keeps the live counts (bergdb 030-01, steps 5, 3 and 4), with
the merges' loop and root collapse, given their live merge and root collapse
(`MergeLiveOK`, `CollapseLiveOK`). -/
theorem liveDel_fullTimeChainF_live (p : Params) (R : Struct BVal → Time → Prop) (hM : 2 ≤ p.M)
    (hsa2 : 2 ≤ p.splitAbove) (hcap : 1 ≤ p.mergeMax) (hp : MergeParamsOK p)
    (hRL : ∀ P t, R P t → RunLinksOK p P t)
    (hRP : ∀ P t, R P t → PointersOK P) (hRK : ∀ P t, R P t → KindsAllOK p P)
    (hML : ∀ ts (tx : Tx), MergeLiveOK (ctxOf p ts) (viewOf (treeRun p ts)) tx.base
      (htOracleOf p (treeRun p ts)))
    (hCL : ∀ ts (tx : Tx), CollapseLiveOK (ctxOf p ts) (viewOf (treeRun p ts)) tx.base) :
    ∀ ts tx, Within p (ts ++ [tx]) → R (treeRun p ts) ts.length → ∀ z top,
      lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z →
      topOf p (ctxOf p ts).view z = .ok top →
      ∀ pre op post, tx.ops = pre ++ op :: post →
      ∀ r w, (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
      SJ0 p ts tx w → TakeJ2 (ctxOf p ts) (viewOf (treeRun p ts)) tx.base w →
      ∀ key, op = .del key → DelFullTimeChainFM (ctxOf p ts) (viewOf (treeRun p ts)) w op →
      WriterWP (putKv op) (ctxOf p ts) w (fun _ w' =>
        LiveEdges p (wNode p (viewOf (treeRun p ts)) w') (ts.length + 1) w'.top.rootKey) := by
  intro ts tx hw hr z top hz htop pre op post hops r w hpre hS hJ key hop hPc
  have hm : (ctxOf p ts).p.merges = true := by
    obtain ⟨_, _, _, _, _, hm, _⟩ := hPc
    exact hm
  obtain ⟨hv, hk, _, _⟩ := kd_contextR p hM ts tx (hRP _ _ hr) (hRK _ _ hr) hw top pre (op :: post) hops r w hpre
  have hICEk : ICEFromKinds (ctxOf p ts) (viewOf (treeRun p ts)) (kindOracleOf p (treeRun p ts)) tx.base :=
    fun v hb hi hun => innerChildren_of_kinds p (treeRun p ts) tx.base (ctxOf p ts) v rfl (hRK _ _ hr)
      (hRP _ _ hr) hb hi.cache hun
  obtain ⟨hvo, hkw, _⟩ := hS.2.1
  have hB := putBase_of_run p ts tx hw (hRL _ _ hr)
  refine liveDel_fullTimeChainF p R hM hsa2 hp hRL hRP hRK ts tx hw hr z top hz htop pre op post hops r w hpre
    hS hJ key hop hPc _ (fun v hv => by
      unfold fresh
      simp only [writerWP_bind, writerWP_get, writerWP_set, writerWP_pure]
      exact hv) ?_
  intro g v hD hpb hhi hLH
  exact writerWP_afterDelete_live key g (ctxOf p ts) _ (viewCoherent_ctxOf p ts) hm _ tx.base hv hk hICEk
    hsa2 hcap (by simp [ctxOf]) hvo hkw top hB (hML ts tx) (hCL ts tx) v
    (delInvJAE_of_T _ _ _ _ _ v hD) hpb hhi hLH


/-! ## What is left of R4, and the successor top theorem -/

/-- What is left of R4: the full leaf split in time below a parent without room,
its copy a hole: below an inner parent, fewer than m live klongs. -/
def DelFullTimeHoleM (c : Ctx) (base : View BVal) (w : W) (op : Op) : Prop :=
  DelFullTimeCascM c base w op ∧ ∀ pre cv L n, op = .del (pre ++ [cv]) → KeyLeaf c base w pre cv L n →
    ∃ q qn k1, TReach (wNode c.p base w) c.i w.top.rootKey q ∧ wNode c.p base w q = some qn ∧
      (k1, L) ∈ qn.liveAt c.i ∧ qn.leaf = false ∧
      ((n.lastVersionGivenDel c.i (bitsUnion n.lastBitmap (n.bitsOf cv))).liveAt c.i).length <
        c.p.mergeBelow

/-- R4's case from its hole part: the copy filled is proved (`liveDel_fullTimeChainF`). -/
theorem delCaseLive_timeCasc_of_hole (p : Params) (R : Struct BVal → Time → Prop) (hM : 2 ≤ p.M)
    (hsa2 : 2 ≤ p.splitAbove) (hp : MergeParamsOK p)
    (hRL : ∀ P t, R P t → RunLinksOK p P t)
    (hRP : ∀ P t, R P t → PointersOK P) (hRK : ∀ P t, R P t → KindsAllOK p P)
    (h : DelCaseLive p R DelFullTimeHoleM) : DelCaseLive p R DelFullTimeCascM := by
  intro ts tx hw hr z top hz htop pre op post hops r w hpre hS hJ key hop hPc Q hfresh hA
  obtain ⟨⟨pre0, cv, L, n, hop', hm, hK, hne, hkeep, hfull, hTP⟩, hcase⟩ := hPc
  obtain ⟨hnm, hnr, _⟩ := hcase pre0 cv L n hop' hK
  by_cases hfill : ∀ q qn k1, TReach (wNode (ctxOf p ts).p (viewOf (treeRun p ts)) w) (ctxOf p ts).i
      w.top.rootKey q → wNode (ctxOf p ts).p (viewOf (treeRun p ts)) w q = some qn →
      (k1, L) ∈ qn.liveAt (ctxOf p ts).i → qn.leaf = false →
      (ctxOf p ts).p.mergeBelow ≤ ((n.lastVersionGivenDel (ctxOf p ts).i
        (bitsUnion n.lastBitmap (n.bitsOf cv))).liveAt (ctxOf p ts).i).length
  · exact liveDel_fullTimeChainF p R hM hsa2 hp hRL hRP hRK ts tx hw hr z top hz htop pre op post hops r w
      hpre hS hJ key hop ⟨pre0, cv, L, n, hop', hm, hK, hne, hkeep, hfull, hTP, hnm, hnr, hfill⟩ Q hfresh hA
  · refine h ts tx hw hr z top hz htop pre op post hops r w hpre hS hJ key hop
      ⟨⟨⟨pre0, cv, L, n, hop', hm, hK, hne, hkeep, hfull, hTP⟩, hcase⟩, ?_⟩ Q hfresh hA
    have hex : ∃ q qn k1, TReach (wNode (ctxOf p ts).p (viewOf (treeRun p ts)) w) (ctxOf p ts).i
        w.top.rootKey q ∧ wNode (ctxOf p ts).p (viewOf (treeRun p ts)) w q = some qn ∧
        (k1, L) ∈ qn.liveAt (ctxOf p ts).i ∧ qn.leaf = false ∧
        ((n.lastVersionGivenDel (ctxOf p ts).i (bitsUnion n.lastBitmap (n.bitsOf cv))).liveAt
          (ctxOf p ts).i).length < (ctxOf p ts).p.mergeBelow := by
      apply Classical.byContradiction
      intro hno
      apply hfill
      intro q qn k1 hq hqn hk hql
      apply Classical.byContradiction
      intro hlt
      exact hno ⟨q, qn, k1, hq, hqn, hk, hql, by omega⟩
    intro pre' cv' L' n' hop'' hK'
    rw [hop'] at hop''
    injection hop'' with hk
    obtain ⟨h1, h2⟩ := List.append_inj hk (by simpa using congrArg List.length hk)
    have h3 : cv = cv' := by simpa using h2
    subst h1 h3
    obtain ⟨_, hrk', hL', hn', hnl'⟩ := hK'
    exact keyLeaf_all2 hK hrk' (fun L1 m => ∃ q qn k1, TReach (wNode (ctxOf p ts).p (viewOf (treeRun p ts)) w)
        (ctxOf p ts).i w.top.rootKey q ∧ wNode (ctxOf p ts).p (viewOf (treeRun p ts)) w q = some qn ∧
        (k1, L1) ∈ qn.liveAt (ctxOf p ts).i ∧ qn.leaf = false ∧
        ((m.lastVersionGivenDel (ctxOf p ts).i (bitsUnion m.lastBitmap (m.bitsOf cv))).liveAt
          (ctxOf p ts).i).length < (ctxOf p ts).p.mergeBelow) hex L' n' hL' hn' hnl'

/-- The merge's tail with its parent full in the cases left after l4c's last part
(`MergeTailFullRest6OK`) at the contexts of the runs of R. -/
def MergeTailRuns6 (p : Params) (R : Struct BVal → Time → Prop) : Prop :=
  ∀ ts (tx : Tx), Within p (ts ++ [tx]) → R (treeRun p ts) ts.length →
    MergeTailFullRest6OK (ctxOf p ts) (viewOf (treeRun p ts)) tx.base (htOracleOf p (treeRun p ts))

/-- `MergeTailRuns4` from `MergeTailRuns6` (`mergeTailFullRest5OK_of_rest6`,
`mergeTailFullRest4OK_of_rest5`). -/
theorem mergeTailRuns4_of_6 (p : Params) (hp : MergeParamsOK p) (R : Struct BVal → Time → Prop)
    (hRL : ∀ P t, R P t → RunLinksOK p P t) (hRK : ∀ P t, R P t → KindsAllOK p P)
    (hRH : ∀ P t, R P t → HeightAllOK p P t) (h6 : MergeTailRuns6 p R) : MergeTailRuns4 p R := by
  intro ts tx hw hr
  have hp' := hp
  unfold MergeParamsOK at hp'
  have hm : (ctxOf p ts).p.merges = true := by
    show p.merges = true
    unfold Params.merges; simp only [decide_eq_true_eq]; omega
  exact mergeTailFullRest4OK_of_rest5 (ctxOf p ts) _ (viewCoherent_ctxOf p ts) hm hp
    (mergeTailFullRest5OK_of_rest6 (ctxOf p ts) _ (viewCoherent_ctxOf p ts) hm hp
      (viewHtOK_of_run p ts tx hw (hRL _ _ hr) (hRK _ _ hr) (hRH _ _ hr)) (h6 ts tx hw hr))

/-- `invGetScanOK_merges_noL4b` with l4c's last merge tail (`MergeTailRuns6`) and R4
narrowed to its hole (`DelFullTimeHoleM`). Its premise `R3Calls` is believed false
at unreached states (030-01's log), so this theorem is believed vacuous until R3
is restated with a made-for fact carried to `afterDelete`'s call. -/
theorem invGetScanOK_merges_noL4c (p : Params) (hp : MergeParamsOK p)
    (hth : 2 ≤ p.theta ∨ p.theta = 0)
    (hF : MergeTailRuns6 p (RunTreeQ p (LatestQD p))) (hR3 : R3Calls p (RunTreeQ p (LatestQD p)))
    (hR4 : DelCaseLive p (RunTreeQ p (LatestQD p)) DelFullTimeHoleM)
    (hCasc : DelCaseLive p (RunTreeQ p (LatestQD p)) DelEmptyCascM) :
    InvPreserved p ∧ GetOK p ∧ ScanOK p ∧ LatestGetOK p ∧ LatestScanOK p := by
  have hp' := hp
  unfold MergeParamsOK at hp'
  have hM := mergeParamsOK_M p hp
  have hRL : ∀ P t, RunTreeQ p (LatestQD p) P t → RunLinksOK p P t := fun _ _ h => h.1
  have hRP : ∀ P t, RunTreeQ p (LatestQD p) P t → PointersOK P := fun _ _ h => h.1.1
  have hRK : ∀ P t, RunTreeQ p (LatestQD p) P t → KindsAllOK p P := fun _ _ h => h.2.2.1.2.2.1
  have hRH : ∀ P t, RunTreeQ p (LatestQD p) P t → HeightAllOK p P t := fun _ _ h => h.2.2.1.2.2.2.1
  exact invGetScanOK_merges_noL4b p hp hth (mergeTailRuns4_of_6 p hp _ hRL hRK hRH hF) hR3
    (delCaseLive_timeCasc_of_hole p _ (by omega) (by omega) hp hRL hRP hRK hR4) hCasc

end SIS.Tree
