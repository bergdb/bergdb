/-
The delete's full leaf split in space with its cascade (bergdb 030-01, step 5):
after a space split no hole is left (both halves are `HalfOK`), so the parent's
klongs to the halves go up through `writerWP_appendKlongs_chainGL`, whatever
the parents' room: the live counts of the tree with the halves in place and the
parent's klongs put (`liveEdgesX_spaceSplit_gen`) are kept by the cascade's walk.
-/
import SIS.Tree.LiveDelSpace

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

set_option maxHeartbeats 8000000 in
/-- A full node X (D + 1) that the transaction did not make, split in space with a
last version given (a delete's), below an inner parent X D, and its cascade
(`writerWP_appendKlongs_chainGL`'s premises for X 0 .. X D): from the live counts
at the start, with halves that are `HalfOK` and hold the node's live klongs, the
divider in the range of the parent's link, they hold after, with no hole. -/
theorem writerWP_handleFull_spaceChain_live (c : Ctx) (base : View BVal)
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
    (hfirst : (Nn (D + 1)).firstTime ≠ some c.i) (hql : (Nn D).leaf = false)
    (hsplit : c.p.splitAbove < last.size)
    (hf : ∀ c' z, (c', z) ∈ (halves (Nn (D + 1)).leaf c.i last []).1.liveAt c.i →
      c' < (halves (Nn (D + 1)).leaf c.i last []).2.2 ∧ (c', z) ∈ (Nn (D + 1)).liveAt c.i)
    (hs : ∀ c' z, (c', z) ∈ (halves (Nn (D + 1)).leaf c.i last []).2.1.liveAt c.i →
      ∃ c0, (halves (Nn (D + 1)).leaf c.i last []).2.2 ≤ c0 ∧
        c' = splitLocalCv (Nn (D + 1)).leaf (halves (Nn (D + 1)).leaf c.i last []).2.2 c0 ∧
        (c0, z) ∈ (Nn (D + 1)).liveAt c.i)
    (hfH : HalfOK c.p c.i (halves (Nn (D + 1)).leaf c.i last []).1)
    (hsH : HalfOK c.p c.i (halves (Nn (D + 1)).leaf c.i last []).2.1)
    (hrK : K (D + 1) ≤ (halves (Nn (D + 1)).leaf c.i last []).2.2 ∧
      ∀ c'' z', (c'', z') ∈ (Nn D).live → K (D + 1) < c'' →
        (halves (Nn (D + 1)).leaf c.i last []).2.2 < c'')
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
      false) c w (fun _ w' => LiveEdges c.p (wNode c.p base w') c.i w'.top.rootKey) := by
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
  apply writerWP_handleFullWith_space_up_last D (X (D + 1)) (X D) (Nn (D + 1)) (Nn D) (K (D + 1)) last
    c w hlk hlq hql hfirst hsplit hpq hpk
  intro w1 h1n h1t h1top h1path h1next h1vals
  obtain ⟨hfl, hsl⟩ := halves_leaf_eq (Nn (D + 1)).leaf c.i last []
  generalize hout : halves (Nn (D + 1)).leaf c.i last [] = out at hf hs hfH hsH hrK hfl hsl h1n ⊢
  have h12 : w.next ≠ w.next + 2 := by omega
  have hN1 : wNode c.p base w1 = updN (updN (wNode c.p base w) w.next out.1) (w.next + 2) out.2.1 :=
    wNode_two_updN c.p base w w1 _ _ _ _ h1n h1t h12 htk0 htk2'
  have hq1wf := KNode.add_key_wf (Nn D) c.i (K (D + 1)) w.next hqwf
  have hq1t := KNode.add_times (Nn D) c.i (.key (K (D + 1)) w.next) (fun s h => by cases h) hqtimes
  have hqlinks : ∀ c' z, (c', z) ∈ ([(K (D + 1), w.next), (out.2.2, w.next + 2)].foldl
      (fun n (cv, y) => n.add c.i (.key cv y)) (Nn D)).liveAt c.i →
      (c' = out.2.2 ∧ z = w.next + 2) ∨ (c' ≠ out.2.2 ∧ c' = K (D + 1) ∧ z = w.next) ∨
      (c' ≠ out.2.2 ∧ c' ≠ K (D + 1) ∧ (c', z) ∈ (Nn D).liveAt c.i) := by
    intro c' z h
    simp only [List.foldl_cons, List.foldl_nil] at h
    rcases KNode.add_key_liveAt_mem _ c.i _ _ hq1wf hq1t c' z h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h1, h2⟩
    · rcases KNode.add_key_liveAt_mem _ c.i _ _ hqwf hqtimes c' z h2 with ⟨h3, h4⟩ | ⟨h3, h4⟩
      · exact Or.inr (Or.inl ⟨h1, h3, h4⟩)
      · exact Or.inr (Or.inr ⟨h1, h3, h4⟩)
  have hXn1 : X (D + 1) ≠ w.next := by have := hXlt (D + 1) (Nat.le_refl _); omega
  have hXn2 : X (D + 1) ≠ w.next + 2 := by have := hXlt (D + 1) (Nat.le_refl _); omega
  have hQn1 : X D ≠ w.next := by have := hXlt D (by omega); omega
  have hQn2 : X D ≠ w.next + 2 := by have := hXlt D (by omega); omega
  have hq'l : ([(K (D + 1), w.next), (out.2.2, w.next + 2)].foldl
      (fun n (cv, y) => n.add c.i (.key cv y)) (Nn D)).leaf = (Nn D).leaf := by
    simp only [List.foldl_cons, List.foldl_nil, KNode.add_leaf]
  have hN'1 : updN (wNode c.p base w1) (X D) ([(K (D + 1), w.next), (out.2.2, w.next + 2)].foldl
      (fun n (cv, y) => n.add c.i (.key cv y)) (Nn D)) w.next = some out.1 := by
    rw [updN_ne _ _ _ _ hQn1.symm, hN1, updN_ne _ _ _ _ h12]; exact updN_self _ _ _
  have hN'2 : updN (wNode c.p base w1) (X D) ([(K (D + 1), w.next), (out.2.2, w.next + 2)].foldl
      (fun n (cv, y) => n.add c.i (.key cv y)) (Nn D)) (w.next + 2) = some out.2.1 := by
    rw [updN_ne _ _ _ _ hQn2.symm, hN1]; exact updN_self _ _ _
  have hoth : ∀ z, z ≠ X (D + 1) → z ≠ X D → z ≠ w.next → z ≠ w.next + 2 →
      updN (wNode c.p base w1) (X D) ([(K (D + 1), w.next), (out.2.2, w.next + 2)].foldl
        (fun n (cv, y) => n.add c.i (.key cv y)) (Nn D)) z = wNode c.p base w z := by
    intro z _ hz2 hz3 hz4
    rw [updN_ne _ _ _ _ hz2, hN1, updN_ne _ _ _ _ hz4, updN_ne _ _ _ _ hz3]
  have hfreshV : ∀ z, (z = w.next ∨ z = w.next + 2) → ∀ u c',
      TReach (wNode c.p base w) c.i w.top.rootKey u → ¬ TLink (wNode c.p base w) c.i u c' z := by
    intro z hz u c' _ hl
    have := hS6 u c' z hl
    rcases hz with hz | hz <;> omega
  obtain ⟨hT1V, hR1V⟩ := treeOK_spaceSplit_gen (wNode c.p base w)
    (updN (wNode c.p base w1) (X D) ([(K (D + 1), w.next), (out.2.2, w.next + 2)].foldl
      (fun n (cv, y) => n.add c.i (.key cv y)) (Nn D))) c.i w.top.rootKey (X D)
    (X (D + 1)) w.next (w.next + 2) (Nn D) (Nn (D + 1)) out.1 out.2.1
    ([(K (D + 1), w.next), (out.2.2, w.next + 2)].foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn D))
    (K (D + 1)) out.2.2 (splitLocalCv (Nn (D + 1)).leaf out.2.2) hS3 (hS4 D (by omega)) hwq hkl hwx
    (updN_self _ _ _) hqlinks hN'1 hN'2 hf hs hoth hwnext hwnext2 h12 hfreshV
  have hLV := liveEdgesX_spaceSplit_gen c.p (fun _ => False) (wNode c.p base w)
    (updN (wNode c.p base w1) (X D) ([(K (D + 1), w.next), (out.2.2, w.next + 2)].foldl
      (fun n (cv, y) => n.add c.i (.key cv y)) (Nn D))) c.i w.top.rootKey (X D)
    (X (D + 1)) w.next (w.next + 2) (Nn D) (Nn (D + 1)) out.1 out.2.1
    ([(K (D + 1), w.next), (out.2.2, w.next + 2)].foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn D))
    (K (D + 1)) out.2.2 (splitLocalCv (Nn (D + 1)).leaf out.2.2) hS3 (hS4 D (by omega)) hwq hkl hwx
    (updN_self _ _ _) hqlinks hN'1 hN'2 hf hs hoth hwnext hwnext2 h12 hfreshV
    (fun h => h) (fun h => h) hfl hsl hfH hsH hq'l
    (addKeys_liveAt_length c.i [(K (D + 1), w.next), (out.2.2, w.next + 2)] (Nn D) hqwf hqtimes)
    ((liveEdgesX_false_iff _ _ _ _).mpr hL)
  have hR2 : ¬ TReach (updN (wNode c.p base w) w.next out.1) c.i w.top.rootKey (w.next + 2) :=
    fun h => hyR (w.next + 2) (by omega)
      (tReach_updN_unreach _ c.i _ _ _ (hyR w.next (Nat.le_refl _)) _ h)
  have hpar := hchain w1 [(K (D + 1), w.next), (out.2.2, w.next + 2)]
    (Or.inr ⟨_, _, _, _, rfl, hrK.1, fun c'' z'' hm hlt => hrK.2 c'' z'' hm hlt⟩)
    (by
      intro q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with hq | hq <;> rw [hq, h1next] <;> simp <;> omega)
    (by rw [h1path, hS1])
    (by
      intro i _ h2
      obtain ⟨a, b⟩ := hS2 i (by omega)
      refine ⟨?_, by rw [h1t]; exact b⟩
      rw [h1n]
      have h1' : ¬ X i = w.next := by have := hXlt i (by omega); omega
      have h2' : ¬ X i = w.next + 2 := by have := hXlt i (by omega); omega
      simp only [h1', h2', ↓reduceIte, a])
    (by
      rw [hN1, h1top]
      exact treeOK_updN_unreach _ c.i _ _ _
        (treeOK_updN_unreach _ c.i _ _ _ hS3 (hyR w.next (Nat.le_refl _))) hR2)
    (by
      intro i _ h2
      rw [hN1, h1top]
      obtain ⟨a, ha⟩ := (hS4 i (by omega)).pathLen
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
      rw [hN1] at hl
      obtain ⟨m, hm, hc⟩ := hl
      by_cases hu2 : u = w.next + 2
      · rw [hu2, updN_self] at hm
        simp only [Option.some.injEq] at hm
        subst hm
        obtain ⟨c0, _, _, h3⟩ := hs c' z hc
        have := hS6 _ c0 z ⟨_, hwx, h3⟩; omega
      · rw [updN_ne _ _ _ _ hu2] at hm
        by_cases hu1 : u = w.next
        · rw [hu1, updN_self] at hm
          simp only [Option.some.injEq] at hm
          subst hm
          have := hS6 _ c' z ⟨_, hwx, (hf c' z hc).2⟩; omega
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
    simp only [hXn1, hXn2, ↓reduceIte, hlk]
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

/-! ## The case: the full leaf split in space below an inner parent, with the cascade -/

/-- As `DelFullSpaceRoomM`, with no room asked of the parent (inner): the halves'
klongs go up through the cascade. -/
def DelFullSpaceChainM (c : Ctx) (base : View BVal) (w : W) (op : Op) : Prop :=
  ∃ pre cv L n, op = .del (pre ++ [cv]) ∧ c.p.merges = true ∧ KeyLeaf c base w pre cv L n ∧
    bitsUnion n.lastBitmap (n.bitsOf cv) ≠ n.lastBitmap ∧
    n.allKeysIn (bitsUnion n.lastBitmap (n.bitsOf cv)) = false ∧
    ¬ ((∃ old, n.ks.getLast? = some (.del old)) ∧ n.lastTime = some c.i) ∧ c.p.M ≤ n.size + 1 ∧
    c.p.splitAbove < (n.lastVersionGivenDel c.i (bitsUnion n.lastBitmap (n.bitsOf cv))).size ∧
    n.firstTime ≠ some c.i ∧ L ≠ w.top.rootKey ∧
    ∀ q qn k1, TReach (wNode c.p base w) c.i w.top.rootKey q → wNode c.p base w q = some qn →
      (k1, L) ∈ qn.liveAt c.i → qn.leaf = false

set_option maxHeartbeats 4000000 in
/-- The full leaf not made by the transaction, split in space below an inner
parent, with the cascade, calls `afterDelete` with the live counts (no hole), in the
stratum (bergdb 030-01, step 5): any `afterDelete` that keeps the live counts from
the hole at (g, 0) gives them after. -/
theorem liveDel_fullSpaceChain (p : Params) (R : Struct BVal → Time → Prop) (hM : 2 ≤ p.M)
    (hsa2 : 2 ≤ p.splitAbove) (hp : MergeParamsOK p)
    (hRL : ∀ P t, R P t → RunLinksOK p P t)
    (hRP : ∀ P t, R P t → PointersOK P) (hRK : ∀ P t, R P t → KindsAllOK p P) :
    ∀ ts tx, Within p (ts ++ [tx]) → R (treeRun p ts) ts.length → ∀ z top,
      lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z →
      topOf p (ctxOf p ts).view z = .ok top →
      ∀ pre op post, tx.ops = pre ++ op :: post →
      ∀ r w, (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
      SJ0 p ts tx w → TakeJ2 (ctxOf p ts) (viewOf (treeRun p ts)) tx.base w →
      ∀ key, op = .del key → DelFullSpaceChainM (ctxOf p ts) (viewOf (treeRun p ts)) w op →
      ∀ Q : W → Prop, (∀ v, Q v → WriterWP fresh (ctxOf p ts) v (fun _ v' => Q v')) →
      (∀ g v, DelInvJT (ctxOf p ts) (viewOf (treeRun p ts)) (kindOracleOf p (treeRun p ts))
          tx.base tx.base v → PutBook (ctxOf p ts) tx.base top v →
        HtInv (htOracleOf p (treeRun p ts)) tx.base (ctxOf p ts) v →
        LiveHoleW key g 0 (ctxOf p ts) (viewOf (treeRun p ts)) v →
        WriterWP (afterDelete key g 0) (ctxOf p ts) v (fun _ v' => Q v')) →
      WriterWP (putKv op) (ctxOf p ts) w (fun _ w' => Q w') := by
  intro ts tx hw hr z top _ htop ops op post hops r w hpre hS hJ key hop hPc Q hfresh hA
  obtain ⟨pre, cv, L0, n0, hop', _, hK, hne0, hkeep0, htd0, hsz0, hsp0, hnm0, hnr0, hpar0⟩ := hPc
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
  obtain ⟨hne, hkeep, htd, hsz, hsp, hnm, hnr, hpar⟩ := keyLeaf_all2 hK hrk
    (fun L' m => bitsUnion m.lastBitmap (m.bitsOf cv) ≠ m.lastBitmap ∧
      m.allKeysIn (bitsUnion m.lastBitmap (m.bitsOf cv)) = false ∧
      ¬ ((∃ old, m.ks.getLast? = some (.del old)) ∧ m.lastTime = some (ctxOf p ts).i) ∧
      (ctxOf p ts).p.M ≤ m.size + 1 ∧
      (ctxOf p ts).p.splitAbove <
        (m.lastVersionGivenDel (ctxOf p ts).i (bitsUnion m.lastBitmap (m.bitsOf cv))).size ∧
      m.firstTime ≠ some (ctxOf p ts).i ∧ L' ≠ w.top.rootKey ∧
      ∀ q qn k1, TReach (wNode (ctxOf p ts).p (viewOf (treeRun p ts)) w) (ctxOf p ts).i w.top.rootKey q →
        wNode (ctxOf p ts).p (viewOf (treeRun p ts)) w q = some qn →
        (k1, L') ∈ qn.liveAt (ctxOf p ts).i → qn.leaf = false)
    ⟨hne0, hkeep0, htd0, hsz0, hsp0, hnm0, hnr0, hpar0⟩ L n hL hn hnl
  have hfull : ¬ DelRoom (ctxOf p ts) cv n := by
    rintro (⟨h1, h2, _⟩ | ⟨_, h2, _⟩)
    · exact htd ⟨h1, h2⟩
    · omega
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
  have hqleaf := hpar _ qm kq hqR hqm hkq
  have hI3 := putInv_of_readsAs _ _ w w3 hI hr03
  -- the halves
  obtain ⟨rr, _, hrN, hdiv, hfh, hsh⟩ := delLast_halves n (ctxOf p ts).i cv (ctxOf p ts).p.splitAbove hnl hsa2 hsp
  obtain ⟨hfH, hsH⟩ := halves_del_halfOK p hp n (ctxOf p ts).i _ hsp
  generalize hlast : n.lastVersionGivenDel (ctxOf p ts).i (bitsUnion n.lastBitmap (n.bitsOf cv)) = last
    at hsp hfh hsh hfH hsH hdiv
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
    refine writerWP_appendDeleteKlong_bitmapFull L P.length cv n _ w3 hlk3 hne htd hsz _ ?_
    generalize hw4 : ({ w3 with trail := "bitmap.full" :: w3.trail } : W) = w4
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
    have hKD1 : ((P[d' + 1 - 1]?).bind (·.1)).getD 0 = kq := by
      rw [show d' + 1 - 1 = d' by omega, hPq]; rfl
    have hXD1 : nodeAt w.top.rootKey P (d' + 1) = L := by rw [← hd']; exact hXD
    -- the divider in the range of the parent's link
    have hqRS : ReachS (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey q :=
      tReach_reachS _ _ _ _ hqR
    obtain ⟨hP1, hP2⟩ := mrg_child_range (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1)
      w.top.rootKey hRO q qm hqRS hqm hqleaf kq L n hkq hn
    have hrrL : (rr.1, rr.2) ∈ n.liveAt (ts.length + 1) := by
      rw [KNode.liveAt_of_times n (ts.length + 1) htn]; exact hrN
    have hrK : kq ≤ rr.1 ∧ ∀ c'' z', (c'', z') ∈ qm.live → kq < c'' → rr.1 < c'' := by
      refine ⟨?_, fun c'' z' hz hlt => ?_⟩
      · rcases Nat.eq_zero_or_pos kq with hk0 | hk0
        · omega
        · exact (hP1 rr.1 rr.2 hrrL).1 hnl hk0
      · exact hP2 c'' z' (by rw [KNode.liveAt_of_times _ (ts.length + 1) (hI.times q qm hqm)]; exact hz)
          hlt rr.1 rr.2 hrrL
    rw [hlast]
    rw [← hXD]
    unfold handleFull
    rw [hd']
    have hmain := writerWP_handleFull_spaceChain_live (ctxOf p ts) (viewOf (treeRun p ts)) w4.path d'
      (fun i => nodeAt w.top.rootKey P i) (fun i => ((P[i - 1]?).bind (·.1)).getD 0)
      (fun i => (wNode (ctxOf p ts).p (viewOf (treeRun p ts)) w (nodeAt w.top.rootKey P i)).getD ⟨true, []⟩)
      last hX4 hK4 hlink4
      (fun i h1 hi hNR hql' c' z hz hpos' =>
        rangeG_of_rangeOrder (ctxOf p ts) _ _ hRO4 htm4 _ _ _ _ _
          (hreach4 (i - 1) (by omega)) (hw4X (i - 1) (by omega)) hql' (hlink4 i h1 (by omega))
          (hw4X i (by omega)) hNR c' z hz hpos')
      (fun i _ hi hNR hsp' => lenG_of_splitAbove (ctxOf p ts) _ _ hsa2 _ _ (hreach4 i (by omega))
        (hw4X i (by omega)) hNR hsp')
      (fun i hi => hwf4 _ _ (hw4X i hi)) (fun i hi => htm4 _ _ (hw4X i hi))
      (fun i i' hi hi' he => hdist4 i i' hi hi' he)
      (by (try simp only []); rw [hNnD1]; exact hnm)
      (by (try simp only []); rw [hNnD]; exact hqleaf) hsp
      (by
        (try simp only []); rw [hNnD1]
        intro c' z' h
        obtain ⟨h1, h2⟩ := hfh c' z' h
        exact ⟨by rw [hdiv]; exact h1, hsub _ (by rw [← hlastN]; exact h2)⟩)
      (by
        (try simp only []); rw [hNnD1]
        intro c' z' h
        obtain ⟨c0, h1, h2, h3⟩ := hsh c' z' h
        exact ⟨c0, by rw [hdiv]; exact h1, by rw [hdiv]; exact h2, hsub _ (by rw [← hlastN]; exact h3)⟩)
      (by (try simp only []); rw [hNnD1]; exact hfH) (by (try simp only []); rw [hNnD1]; exact hsH)
      (by (try simp only []); rw [hNnD1, hNnD, hKD1, hdiv]; exact hrK)
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

/-- The full leaf not made by the transaction, split in space below an inner
parent, with the cascade, keeps the live counts (bergdb 030-01, steps 5, 3 and 4), with
the merges' loop and root collapse, given their live merge and root collapse
(`MergeLiveOK`, `CollapseLiveOK`). -/
theorem liveDel_fullSpaceChain_live (p : Params) (R : Struct BVal → Time → Prop) (hM : 2 ≤ p.M)
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
      ∀ key, op = .del key → DelFullSpaceChainM (ctxOf p ts) (viewOf (treeRun p ts)) w op →
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
  refine liveDel_fullSpaceChain p R hM hsa2 hp hRL hRP hRK ts tx hw hr z top hz htop pre op post hops r w hpre
    hS hJ key hop hPc _ (fun v hv => by
      unfold fresh
      simp only [writerWP_bind, writerWP_get, writerWP_set, writerWP_pure]
      exact hv) ?_
  intro g v hD hpb hhi hLH
  exact writerWP_afterDelete_live key g (ctxOf p ts) _ (viewCoherent_ctxOf p ts) hm _ tx.base hv hk hICEk
    hsa2 hcap (by simp [ctxOf]) hvo hkw top hB (hML ts tx) (hCL ts tx) v
    (delInvJAE_of_T _ _ _ _ _ v hD) hpb hhi hLH

end SIS.Tree
