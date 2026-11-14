import SIS.Tree.WriterTreeChainG
import SIS.Tree.RangeChain
import SIS.Tree.RangeSteps
import SIS.Tree.RangeOps
import SIS.Tree.RangeLeb

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! Cascades of splits of any kind and depth keep the walk's ranges (bergdb
024-12, TP10; `RangeOrder`): prover cost's `writerWP_appendKlongs_chainG` with
the ranges carried along. -/

/-- A node with links among another's, in place of a node of a tree in order,
keeps the walk's ranges. -/
theorem rangeOrder_updN_sub (N : NodeId → Option KNode) (t : Time) (r x : NodeId) (m m' : KNode)
    (hR : RangeOrder (updN N x m) t r) (hl : m'.leaf = m.leaf)
    (hsub : ∀ c z, (c, z) ∈ m'.liveAt t → (c, z) ∈ m.liveAt t) :
    RangeOrder (updN N x m') t r := by
  refine rangeOrder_shrink (updN N x m) (updN N x m') t r x m m' hR (updN_self _ _ _) ?_ hl hsub
  intro y
  by_cases h : y = x
  · rw [h, updN_self]; simp
  · rw [updN_ne _ _ _ _ h, updN_ne _ _ _ _ h]; simp [h]

/-- `chain_halves_facts` with the divider's compare value live in the node with
the klongs put, and a live compare value below it. -/
theorem chain_halves_factsR (t : Time) (n : KNode) (ins : List (Nat × NodeId))
    (hins : InsOK n ins) (h2 : 2 ≤ n.live.length) (hnt : ∀ s, Klong.time s ∈ n.ks → s ≤ t)
    (hnwf : klongsWf n.ks = true) :
    ∃ r : Nat × NodeId, (halves n.leaf t (n.lastVersion t) ins).2.2 = r.1 ∧ 0 < r.1 ∧
      (∃ zs, (r.1, zs) ∈ (ins.foldl (fun n (cv, y) => n.add t (.key cv y)) n).liveAt t) ∧
      (∃ c0 z0, (c0, z0) ∈ (ins.foldl (fun n (cv, y) => n.add t (.key cv y)) n).liveAt t ∧
        c0 < r.1) ∧
      (∀ c z, (c, z) ∈ (halves n.leaf t (n.lastVersion t) ins).1.liveAt t → c < r.1 ∧
        (c, z) ∈ (ins.foldl (fun n (cv, y) => n.add t (.key cv y)) n).liveAt t) ∧
      (∀ c z, (c, z) ∈ (halves n.leaf t (n.lastVersion t) ins).2.1.liveAt t → ∃ c0, r.1 ≤ c0 ∧
        c = splitLocalCv n.leaf r.1 c0 ∧
        (c0, z) ∈ (ins.foldl (fun n (cv, y) => n.add t (.key cv y)) n).liveAt t) := by
  obtain ⟨r, hr⟩ := divider_exists n (by omega)
  have hrm := divider_mem_live n r hr
  have hsc := divider_pos' n r h2 hr
  obtain ⟨a, more, hins_eq, hside⟩ := hins.side r hrm
  obtain ⟨hdiv, hfh, hsh⟩ := halves_links n.leaf t n rfl a more r hr hsc hside
  rw [← hins_eq] at hdiv hfh hsh
  have hcv : ∀ c z, (c, z) ∈ n.live → ∃ z',
      (c, z') ∈ (ins.foldl (fun n (cv, y) => n.add t (.key cv y)) n).liveAt t := by
    intro c z h
    have hl0 := lookup_of_mem_nodup _ (KNode.live_keys_nodup _) c z h
    obtain ⟨z', hz'⟩ := pairLookupFold_isSome c ins (n.live.lookup c) (by rw [hl0]; rfl)
    exact ⟨z', KNode.addKeys_liveAt_of_fold t ins _ hnwf hnt c z' hz'⟩
  obtain ⟨a0, ha0, ha0r⟩ := live_below_divider n r h2 hr
  refine ⟨r, hdiv, hsc, hcv r.1 r.2 hrm, ?_, ?_, ?_⟩
  · obtain ⟨z', hz'⟩ := hcv a0.1 a0.2 ha0
    exact ⟨a0.1, z', hz', ha0r⟩
  · intro c z h
    obtain ⟨h1, h2'⟩ := hfh c z h
    exact ⟨h1, KNode.addKeys_liveAt_of_fold t ins _ hnwf hnt c z h2'⟩
  · intro c z h
    obtain ⟨c0, h1, h2', h3⟩ := hsh c z h
    exact ⟨c0, h1, h2', KNode.addKeys_liveAt_of_fold t ins _ hnwf hnt c0 z h3⟩

set_option maxHeartbeats 1600000 in
/-- `writerWP_appendKlongs_chainG` (prover cost's) with the walk's ranges: from
a state whose tree with the klongs ins put into X (s + e) is a tree in order
(`RangeOrder`), `appendKlongs (s + e)` keeps the writer's tree and its ranges.
The steps: `rangeOrder_timeStepAny`, `rangeOrder_spaceStep`,
`rangeOrder_spaceInPlaceStep`, `rangeOrder_segSpaceStep`, `rangeOrder_rootTimeStep`,
`rangeOrder_rootSpaceStep` and `rangeOrder_updN_sub`; a node split is reached no
more (`rangeOrder_agree`). -/
theorem writerWP_appendKlongs_chainGRange (c : Ctx) (base : View BVal)
    (path0 : List (Option Nat × NodeId)) (s D : Nat) (X : Nat → NodeId) (K : Nat → Nat)
    (Nn : Nat → KNode)
    (hX : ∀ i, s ≤ i → i ≤ D → (path0[i]?).map (·.2) = some (X i))
    (hK : ∀ i, s < i → i ≤ D → path0[i]? = some (some (K i), X i))
    (hlinkK : ∀ i, s < i → i ≤ D → (K i, X i) ∈ (Nn (i - 1)).liveAt c.i)
    (hrange : ∀ i, s < i → i ≤ D → ¬ ChainRoom c (Nn i) → (Nn (i - 1)).leaf = false →
      ∀ c' z, (c', z) ∈ (Nn i).live → 0 < c' →
      K i ≤ c' ∧ ∀ c'' z', (c'', z') ∈ (Nn (i - 1)).live → K i < c'' → c' < c'')
    (hlen : ∀ i, s ≤ i → i ≤ D → ¬ ChainRoom c (Nn i) →
      c.p.splitAbove < ((Nn i).lastVersion c.i).size →
      2 ≤ (Nn i).live.length)
    (hwf : ∀ i, s ≤ i → i ≤ D → klongsWf (Nn i).ks = true)
    (htimes : ∀ i, s ≤ i → i ≤ D → ∀ t, Klong.time t ∈ (Nn i).ks → t ≤ c.i)
    (htop : ChainRoom c (Nn s) ∨ s = 0)
    (hdist : ∀ i i', s ≤ i → i ≤ D → s ≤ i' → i' ≤ D → X i = X i' → i = i') :
    ∀ e, s + e ≤ D → ∀ (w : W) (ins : List (Nat × NodeId)),
      InsOK (Nn (s + e)) ins → (∀ q ∈ ins, q.2 < w.next) →
      w.path = path0 →
      (∀ i, s ≤ i → i ≤ s + e → w.nodes.lookup (X i) = some (Nn i) ∧ w.taken.contains (X i) = false) →
      TreeOK (wNode c.p base w) c.i w.top.rootKey →
      (∀ i, s ≤ i → i ≤ s + e → TReach (wNode c.p base w) c.i w.top.rootKey (X i)) →
      (∀ z, w.next ≤ z → w.nodes.lookup z = none ∧ w.taken.contains z = false ∧
        knodeOf c.p base z = none) →
      (∀ u c' z, TLink (wNode c.p base w) c.i u c' z → z < w.next) →
      (s = 0 → w.top.rootKey = X 0) →
      TreeOK (updN (wNode c.p base w) (X (s + e))
        (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + e)))) c.i w.top.rootKey →
      RangeOrder (updN (wNode c.p base w) (X (s + e))
        (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + e)))) c.i w.top.rootKey →
      WriterWP (appendKlongs (s + e) (X (s + e)) ins) c w (fun _ w' =>
        TreeOK (wNode c.p base w') c.i w'.top.rootKey ∧
        ((w'.top = w.top ∨ (s = 0 ∧ w.next ≤ w'.top.rootKey)) ∧ w'.taken = w.taken ∧ w'.path = w.path ∧ w.next ≤ w'.next ∧ w'.vals = w.vals) ∧
        (∀ z, z < w.next → (∀ i, s ≤ i → i ≤ s + e → z ≠ X i) →
          w'.nodes.lookup z = w.nodes.lookup z) ∧
        (∀ z, TReach (wNode c.p base w') c.i w'.top.rootKey z →
          TReach (updN (wNode c.p base w) (X (s + e))
            (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + e)))) c.i
            w.top.rootKey z ∨ w.next ≤ z) ∧
        RangeOrder (wNode c.p base w') c.i w'.top.rootKey) := by
  -- the room case at any level
  have hroomCase : ∀ e, s + e ≤ D → ∀ (w : W) (ins : List (Nat × NodeId)),
      w.nodes.lookup (X (s + e)) = some (Nn (s + e)) → w.taken.contains (X (s + e)) = false →
      (Nn (s + e)).size + ins.length + 1 ≤ c.p.M →
      deadOver c.p (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + e))) = false →
      TreeOK (updN (wNode c.p base w) (X (s + e))
        (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + e)))) c.i w.top.rootKey →
      RangeOrder (updN (wNode c.p base w) (X (s + e))
        (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + e)))) c.i w.top.rootKey →
      WriterWP (appendKlongs (s + e) (X (s + e)) ins) c w (fun _ w' =>
        TreeOK (wNode c.p base w') c.i w'.top.rootKey ∧
        ((w'.top = w.top ∨ (s = 0 ∧ w.next ≤ w'.top.rootKey)) ∧ w'.taken = w.taken ∧ w'.path = w.path ∧ w.next ≤ w'.next ∧ w'.vals = w.vals) ∧
        (∀ z, z < w.next → (∀ i, s ≤ i → i ≤ s + e → z ≠ X i) →
          w'.nodes.lookup z = w.nodes.lookup z) ∧
        (∀ z, TReach (wNode c.p base w') c.i w'.top.rootKey z →
          TReach (updN (wNode c.p base w) (X (s + e))
            (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + e)))) c.i
            w.top.rootKey z ∨ w.next ≤ z) ∧
        RangeOrder (wNode c.p base w') c.i w'.top.rootKey) := by
    intro e _ w ins hlk htk hroom hdead hV hVR
    refine writerWP_mono (writerWP_appendKlongs_addKeys (s + e) (X (s + e)) (Nn (s + e)) ins c w hlk
      hroom hdead) ?_
    intro _ w' hw'
    subst hw'
    have hN := wNode_upsert_updN c.p base w { w with nodes := upsert w.nodes (X (s + e)) (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + e))) } (X (s + e)) _ rfl rfl htk
    refine ⟨?_, ⟨Or.inl rfl, rfl, rfl, Nat.le_refl _, rfl⟩, ?_, ?_, ?_⟩
    · rw [hN]; exact hV
    · intro z _ hz
      show (upsert w.nodes _ _).lookup z = _
      rw [lookup_upsert, ite_eq_right_of_eq_false _ _
        (eq_false (hz (s + e) (Nat.le_add_right _ _) (Nat.le_refl _)))]
    · intro z hz
      rw [hN] at hz
      exact Or.inl hz
    · rw [hN]; exact hVR
  intro e
  induction e with
  | zero =>
    intro hD w ins hins hinsT hS1 hS2 hS3 hS4 hS5 hS6 hR0 hV hVR
    obtain ⟨hlk, htk⟩ := hS2 s (Nat.le_refl _) (by omega)
    by_cases hroom : (Nn (s + 0)).size + ins.length + 1 ≤ c.p.M ∧
        deadOver c.p (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + 0))) = false
    · exact hroomCase 0 hD w ins hlk htk hroom.1 hroom.2 hV hVR
    · have hs0 : s = 0 := by
        rcases htop with h | h
        · exfalso
          exact hroom ⟨by have := h.1; have := hins.length; simp only [Nat.add_zero]; omega,
            by simpa using h.2 ins hins.length⟩
        · exact h
      -- the space root splits: a time split or a space split, in place or not
      simp only [Nat.add_zero] at hroom hins hV hVR ⊢
      subst hs0
      have hrk : w.top.rootKey = X 0 := hR0 rfl
      have hV0 : TreeOK (updN (wNode c.p base w) (X 0)
          (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn 0))) c.i (X 0) := by
        rw [hrk] at hV; exact hV
      have hVR0 : RangeOrder (updN (wNode c.p base w) (X 0)
          (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn 0))) c.i (X 0) := by
        rw [hrk] at hVR; exact hVR
      have hNR : ¬ ChainRoom c (Nn 0) := fun ⟨h1, h2⟩ =>
        hroom ⟨by have := hins.length; omega, h2 ins hins.length⟩
      have hXlt0 : X 0 < w.next := by
        rcases Nat.lt_or_ge (X 0) w.next with hlt | hge
        · exact hlt
        · have := (hS5 (X 0) hge).1
          rw [hlk] at this; cases this
      obtain ⟨hfree0, htk0, hbase0⟩ := hS5 w.next (Nat.le_refl _)
      obtain ⟨hfree2, htk2', hbase2⟩ := hS5 (w.next + 2) (by omega)
      obtain ⟨hfree4, htk4, hbase4⟩ := hS5 (w.next + 2 + 2) (by omega)
      have hwfree : ∀ z, w.next ≤ z → wNode c.p base w z = none := by
        intro z hz
        obtain ⟨a, b, d⟩ := hS5 z hz
        simp only [wNode, b, Bool.false_eq_true, ↓reduceIte, a, d]
      have hnoLink : ∀ z, w.next ≤ z → ∀ u c', ¬ TLink (wNode c.p base w) c.i u c' z := by
        intro z hz u c' hl; have := hS6 u c' z hl; omega
      have hwx : wNode c.p base w (X 0) = some (Nn 0) := by
        simp only [wNode, htk, Bool.false_eq_true, ↓reduceIte, hlk]
      have hxtimes := htimes 0 (Nat.le_refl _) (by omega)
      have hxwf := hwf 0 (Nat.le_refl _) (by omega)
      have hvxLinks : ∀ c' z, (c', z) ∈ (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y))
          (Nn 0)).liveAt c.i → z < w.next := by
        intro c' z h
        have hf := KNode.addKeys_liveAt_fold c.i ins _ hxwf hxtimes c' z h
        rcases pairLookupFold_some_mem c' ins _ z hf with hm | hm
        · exact hinsT (c', z) hm
        · have hm' := lookup_some_mem hm
          rw [← KNode.liveAt_of_times _ c.i hxtimes] at hm'
          exact hS6 _ _ _ ⟨_, hwx, hm'⟩
      have hVnone : ∀ z, w.next ≤ z → updN (wNode c.p base w) (X 0)
          (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn 0)) z = none := by
        intro z hz
        rw [updN_ne _ _ _ _ (fun h => by omega)]
        exact hwfree z hz
      have hVfresh : ∀ z, w.next ≤ z → ∀ u c', TReach (updN (wNode c.p base w) (X 0)
          (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn 0))) c.i (X 0) u →
          ¬ TLink (updN (wNode c.p base w) (X 0)
            (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn 0))) c.i u c' z := by
        intro z hz u c' _ hl
        obtain ⟨m, hm, hc⟩ := hl
        by_cases hu : u = X 0
        · rw [hu, updN_self] at hm
          simp only [Option.some.injEq] at hm
          subst hm
          have := hvxLinks c' z hc; omega
        · rw [updN_ne _ _ _ _ hu] at hm
          exact hnoLink z hz u c' ⟨m, hm, hc⟩
      have hlsubOf : ∀ l : KNode, (∀ s, Klong.time s ∈ l.ks → s ≤ c.i) →
          (∀ q', l.live.lookup q' = ins.foldl (pairLookupStep q') ((Nn 0).live.lookup q')) →
          ∀ c' z, (c', z) ∈ (⟨(Nn 0).leaf, l.ks⟩ : KNode).liveAt c.i →
            (c', z) ∈ (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn 0)).liveAt c.i := by
        intro l hl_times hl_look c' z h
        apply KNode.addKeys_liveAt_of_fold c.i ins _ hxwf hxtimes
        have h' : (c', z) ∈ (⟨(Nn 0).leaf, l.ks⟩ : KNode).live := by
          rw [← KNode.liveAt_of_times (⟨(Nn 0).leaf, l.ks⟩ : KNode) c.i hl_times]; exact h
        have hlk' := lookup_of_mem_nodup _ (KNode.live_keys_nodup _) c' z h'
        rw [← hl_look c']
        exact hlk'
      have hTIME0 : ∀ (up : NodeId → List (Nat × NodeId) → M Unit) (compact : Bool),
          (!compact && decide (((Nn 0).lastVersion c.i).size > c.p.splitAbove)) = false →
          WriterWP (handleFullWith up 0 (X 0) ins ((Nn 0).lastVersion c.i) compact) c w (fun _ w' =>
            TreeOK (wNode c.p base w') c.i w'.top.rootKey ∧
            ((w'.top = w.top ∨ (0 = 0 ∧ w.next ≤ w'.top.rootKey)) ∧ w'.taken = w.taken ∧
              w'.path = w.path ∧ w.next ≤ w'.next ∧ w'.vals = w.vals) ∧
            (∀ z, z < w.next → (∀ i, 0 ≤ i → i ≤ 0 → z ≠ X i) →
              w'.nodes.lookup z = w.nodes.lookup z) ∧
            (∀ z, TReach (wNode c.p base w') c.i w'.top.rootKey z →
              TReach (updN (wNode c.p base w) (X 0)
                (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn 0))) c.i
                w.top.rootKey z ∨ w.next ≤ z) ∧
            RangeOrder (wNode c.p base w') c.i w'.top.rootKey) := by
        intro up compact hcs
        by_cases hmade : (Nn 0).firstTime = some c.i
        · -- the root time split in place
          refine writerWP_mono (writerWP_handleFullWith_timeInPlace_term0 up (X 0) (Nn 0) ins compact
            c w hlk hmade hcs) ?_
          rintro _ w' ⟨l, _, _, hl_times, hl_look, h't, h'top, h'v, h'next, h'path, h'n⟩
          have hN' : wNode c.p base w' = updN (wNode c.p base w) (X 0) ⟨(Nn 0).leaf, l.ks⟩ :=
            wNode_upsert_updN c.p base w w' _ _ h'n h't htk
          obtain ⟨hT', hR'⟩ := treeOK_updN_sub (wNode c.p base w) c.i w.top.rootKey (X 0) _ _ hV
            (hlsubOf l hl_times hl_look)
          have hVR' := rangeOrder_updN_sub (wNode c.p base w) c.i w.top.rootKey (X 0) _
            ⟨(Nn 0).leaf, l.ks⟩ hVR (KNode.addKeys_leaf c.i ins (Nn 0)).symm (hlsubOf l hl_times hl_look)
          refine ⟨by rw [hN', h'top]; exact hT', ⟨Or.inl h'top, h't, h'path, by omega, h'v⟩, ?_, ?_,
            by rw [hN', h'top]; exact hVR'⟩
          · intro z _ hzX
            rw [h'n, lookup_upsert, ite_eq_right_of_eq_false _ _
              (eq_false (hzX 0 (Nat.le_refl _) (Nat.le_refl _)))]
          · intro z hz
            rw [hN', h'top] at hz
            exact Or.inl (hR' z hz)
        · -- the root time split: a new root
          refine writerWP_mono (writerWP_handleFullWith_rootTime_term up (X 0) (Nn 0) ins compact c w
            hlk hmade hcs hXlt0 hfree0) ?_
          rintro _ w' ⟨l, _, _, hl_times, hl_look, h't, h'root, h'v, h'path, h'next, h'n⟩
          have hN' : wNode c.p base w' = updN (updN (wNode c.p base w) (X 0)
              ((Nn 0).toPrev (c.i - 1))) w.next ⟨(Nn 0).leaf, l.ks⟩ :=
            wNode_two_updN c.p base w w' _ _ _ _ h'n h't (by omega) htk htk0
          obtain ⟨hT', hR'⟩ := treeOK_rootTimeStep (updN (wNode c.p base w) (X 0)
              (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn 0))) (wNode c.p base w') c.i
            (X 0) w.next (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn 0))
            ⟨(Nn 0).leaf, l.ks⟩ hV0 (updN_self _ _ _)
            (by rw [hN']; exact updN_self _ _ _)
            (hlsubOf l hl_times hl_look)
            (by
              intro z h1 h2
              rw [hN', updN_ne _ _ _ _ h2, updN_ne _ _ _ _ h1]
              exact (updN_ne _ _ _ _ h1).symm)
            (hVnone w.next (Nat.le_refl _))
            (hVfresh w.next (Nat.le_refl _))
          have hVR' := rangeOrder_rootTimeStep (updN (wNode c.p base w) (X 0)
              (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn 0))) (wNode c.p base w') c.i
            (X 0) w.next (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn 0))
            ⟨(Nn 0).leaf, l.ks⟩ hVR0 hV0 (updN_self _ _ _)
            (hVnone w.next (Nat.le_refl _)) (hVfresh w.next (Nat.le_refl _))
            (by rw [hN']; exact updN_self _ _ _)
            (KNode.addKeys_leaf c.i ins (Nn 0)).symm (hlsubOf l hl_times hl_look)
            (by
              intro z h2 h1
              rw [hN', updN_ne _ _ _ _ h2, updN_ne _ _ _ _ h1]
              exact (updN_ne _ _ _ _ h1).symm)
          refine ⟨by rw [h'root]; exact hT', ⟨Or.inr ⟨rfl, by omega⟩, h't, h'path, by omega, h'v⟩,
            ?_, ?_, by rw [h'root]; exact hVR'⟩
          · intro z hz hzX
            rw [h'n]
            have h1' : ¬ z = X 0 := hzX 0 (Nat.le_refl _) (Nat.le_refl _)
            have h2' : ¬ z = w.next := by omega
            simp only [h1', h2', ↓reduceIte]
          · intro z hz
            rw [h'root] at hz
            rcases (hR' z hz).1 with h | h
            · exact Or.inl (by rw [hrk]; exact h)
            · exact Or.inr (by omega)
      have hSPACE0 : ∀ (up : NodeId → List (Nat × NodeId) → M Unit),
          c.p.splitAbove < ((Nn 0).lastVersion c.i).size →
          WriterWP (handleFullWith up 0 (X 0) ins ((Nn 0).lastVersion c.i) false) c w (fun _ w' =>
            TreeOK (wNode c.p base w') c.i w'.top.rootKey ∧
            ((w'.top = w.top ∨ (0 = 0 ∧ w.next ≤ w'.top.rootKey)) ∧ w'.taken = w.taken ∧
              w'.path = w.path ∧ w.next ≤ w'.next ∧ w'.vals = w.vals) ∧
            (∀ z, z < w.next → (∀ i, 0 ≤ i → i ≤ 0 → z ≠ X i) →
              w'.nodes.lookup z = w.nodes.lookup z) ∧
            (∀ z, TReach (wNode c.p base w') c.i w'.top.rootKey z →
              TReach (updN (wNode c.p base w) (X 0)
                (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn 0))) c.i
                w.top.rootKey z ∨ w.next ≤ z) ∧
            RangeOrder (wNode c.p base w') c.i w'.top.rootKey) := by
        intro up hsp
        have h2l := hlen 0 (Nat.le_refl _) (by omega) hNR hsp
        obtain ⟨r, hdiv, hsc, hscL, _, hf, hs⟩ := chain_halves_factsR c.i (Nn 0) ins hins h2l hxtimes hxwf
        by_cases hmade : (Nn 0).firstTime = some c.i
        · -- the root space split in place: the second half and a new root
          refine writerWP_mono (writerWP_handleFullWith_rootSpaceInPlace_term up (X 0) (Nn 0) ins c w
            hlk hmade hsp hXlt0 hfree2) ?_
          rintro _ w' ⟨h't, h'root, h'v, h'path, h'next, h'n⟩
          obtain ⟨out, hout⟩ : ∃ o, halves (Nn 0).leaf c.i ((Nn 0).lastVersion c.i) ins = o :=
            ⟨_, rfl⟩
          rw [hout] at h'n hdiv hf hs
          rw [hdiv] at h'n
          have hFx : ¬ w.next = X 0 := by omega
          have hRx : ¬ w.next + 2 = X 0 := by omega
          have hRF : ¬ w.next + 2 = w.next := by omega
          have hw' : ∀ z, wNode c.p base w' z =
              if z = X 0 then some out.1
              else if z = w.next then some out.2.1
              else if z = w.next + 2 then some ⟨false, [.time c.i, .key 0 (X 0), .key r.1 w.next]⟩
              else wNode c.p base w z := by
            intro z
            by_cases h1 : z = X 0
            · subst h1; simp only [wNode, h't, htk, h'n, Bool.false_eq_true, ↓reduceIte]
            · by_cases h2 : z = w.next
              · subst h2; simp only [wNode, h't, htk0, h'n, h1, Bool.false_eq_true, ↓reduceIte]
              · by_cases h3 : z = w.next + 2
                · subst h3
                  simp only [wNode, h't, htk2', h'n, h1, h2, Bool.false_eq_true, ↓reduceIte]
                · simp only [wNode, h't, h'n, h1, h2, h3, ↓reduceIte]
          have hnd : ([(0, X 0), (r.1, w.next)].map Prod.fst).Nodup := by
            simp only [List.map_cons, List.map_nil, List.nodup_cons, List.mem_cons,
              List.not_mem_nil, or_false, List.nodup_nil, and_true, not_false_eq_true]
            omega
          have hrn : ∀ c' z, (c', z) ∈ (⟨false, [.time c.i, .key 0 (X 0), .key r.1 w.next]⟩ :
              KNode).liveAt c.i → (c' = 0 ∧ z = X 0) ∨ (c' = r.1 ∧ z = w.next) := by
            intro c' z h
            have h' := (mrg_newKlongs_liveAt_iff false c.i [(0, X 0), (r.1, w.next)] hnd c' z).mp h
            simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h'
            exact h'
          obtain ⟨hT', hR'⟩ := treeOK_rootSpaceInPlaceStep (updN (wNode c.p base w) (X 0)
              (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn 0))) (wNode c.p base w') c.i
            (X 0) w.next (w.next + 2) (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn 0))
            out.1 out.2.1 ⟨false, [.time c.i, .key 0 (X 0), .key r.1 w.next]⟩ r.1
            (splitLocalCv (Nn 0).leaf r.1) hsc hV0 (updN_self _ _ _)
            (by rw [hw']; simp only [hRx, hRF, ↓reduceIte])
            hrn
            (by rw [hw']; simp only [↓reduceIte])
            (by rw [hw']; simp only [hFx, ↓reduceIte])
            hf hs
            (by
              intro z h1 h2 h3
              rw [hw']
              simp only [h1, h2, h3, ↓reduceIte]
              exact (updN_ne _ _ _ _ h1).symm)
            (by
              intro z hz
              have hzn : w.next ≤ z := by rcases hz with hz | hz <;> omega
              exact ⟨hVnone z hzn, hVfresh z hzn⟩)
            (by omega)
          have hVR' := rangeOrder_rootSpaceStep (updN (wNode c.p base w) (X 0)
              (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn 0))) (wNode c.p base w') c.i
            (X 0) (X 0) w.next (w.next + 2) (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn 0))
            out.1 out.2.1 ⟨false, [.time c.i, .key 0 (X 0), .key r.1 w.next]⟩ r.1 hVR0 hV0
            (updN_self _ _ _) (Or.inl rfl)
            (hVnone w.next (Nat.le_refl _)) (hVfresh w.next (Nat.le_refl _))
            (hVnone (w.next + 2) (by omega)) (hVfresh (w.next + 2) (by omega))
            (fun h => hFx h.symm) (fun h => hRx h.symm) (by omega)
            hscL hsc
            (by rw [hw']; simp only [hRx, hRF, ↓reduceIte]) rfl hrn
            ((mrg_newKlongs_liveAt_iff false c.i [(0, X 0), (r.1, w.next)] hnd r.1 w.next).mpr
              (by simp))
            (by rw [hw']; simp only [↓reduceIte])
            (by
              have := (halves_leaf_flags (Nn 0).leaf c.i ((Nn 0).lastVersion c.i) ins).1
              rw [hout] at this
              rw [this, KNode.addKeys_leaf])
            (fun c' z h => ⟨(hf c' z h).2, (hf c' z h).1⟩)
            (by rw [hw']; simp only [hFx, ↓reduceIte])
            (by
              have := (halves_leaf_flags (Nn 0).leaf c.i ((Nn 0).lastVersion c.i) ins).2
              rw [hout] at this
              rw [this, KNode.addKeys_leaf])
            (by
              intro c' z h
              obtain ⟨c0, h1, h2, h3⟩ := hs c' z h
              refine ⟨c0, h1, h3, ?_⟩
              rw [h2, splitLocalCv_eq, KNode.addKeys_leaf])
            (by
              intro z h3 h1 h2 _
              rw [hw']
              simp only [h1, h2, h3, ↓reduceIte]
              exact (updN_ne _ _ _ _ h1).symm)
          refine ⟨by rw [h'root]; exact hT', ⟨Or.inr ⟨rfl, by omega⟩, h't, h'path, by omega, h'v⟩,
            ?_, ?_, by rw [h'root]; exact hVR'⟩
          · intro z hz hzX
            rw [h'n]
            have h1' : ¬ z = X 0 := hzX 0 (Nat.le_refl _) (Nat.le_refl _)
            have h2' : ¬ z = w.next := by omega
            have h3' : ¬ z = w.next + 2 := by omega
            simp only [h1', h2', h3', ↓reduceIte]
          · intro z hz
            rw [h'root] at hz
            rcases hR' z hz with h | h | h
            · exact Or.inl (by rw [hrk]; exact h)
            · exact Or.inr (by omega)
            · exact Or.inr (by omega)
        · -- the root space split: the halves and a new root
          refine writerWP_mono (writerWP_handleFullWith_rootSpace_term up (X 0) (Nn 0) ins c w
            hlk hmade hsp hXlt0) ?_
          rintro _ w' ⟨h't, h'root, h'v, h'path, h'next, h'n⟩
          obtain ⟨out, hout⟩ : ∃ o, halves (Nn 0).leaf c.i ((Nn 0).lastVersion c.i) ins = o :=
            ⟨_, rfl⟩
          rw [hout] at h'n hdiv hf hs
          rw [hdiv] at h'n
          have hFx : ¬ w.next = X 0 := by omega
          have hSx : ¬ w.next + 2 = X 0 := by omega
          have hRx : ¬ w.next + 2 + 2 = X 0 := by omega
          have hSF : ¬ w.next + 2 = w.next := by omega
          have hRF : ¬ w.next + 2 + 2 = w.next := by omega
          have hRS : ¬ w.next + 2 + 2 = w.next + 2 := by omega
          have hw' : ∀ z, wNode c.p base w' z =
              if z = X 0 then some ((Nn 0).toPrev (c.i - 1))
              else if z = w.next then some out.1
              else if z = w.next + 2 then some out.2.1
              else if z = w.next + 2 + 2 then
                some ⟨false, [.time c.i, .key 0 w.next, .key r.1 (w.next + 2)]⟩
              else wNode c.p base w z := by
            intro z
            by_cases h1 : z = X 0
            · subst h1; simp only [wNode, h't, htk, h'n, Bool.false_eq_true, ↓reduceIte]
            · by_cases h2 : z = w.next
              · subst h2; simp only [wNode, h't, htk0, h'n, h1, Bool.false_eq_true, ↓reduceIte]
              · by_cases h3 : z = w.next + 2
                · subst h3
                  simp only [wNode, h't, htk2', h'n, h1, h2, Bool.false_eq_true, ↓reduceIte]
                · by_cases h4 : z = w.next + 2 + 2
                  · subst h4
                    simp only [wNode, h't, htk4, h'n, h1, h2, h3, Bool.false_eq_true, ↓reduceIte]
                  · simp only [wNode, h't, h'n, h1, h2, h3, h4, ↓reduceIte]
          have hnd : ([(0, w.next), (r.1, w.next + 2)].map Prod.fst).Nodup := by
            simp only [List.map_cons, List.map_nil, List.nodup_cons, List.mem_cons,
              List.not_mem_nil, or_false, List.nodup_nil, and_true, not_false_eq_true]
            omega
          have hrn : ∀ c' z, (c', z) ∈ (⟨false, [.time c.i, .key 0 w.next, .key r.1 (w.next + 2)]⟩ :
              KNode).liveAt c.i → (c' = 0 ∧ z = w.next) ∨ (c' = r.1 ∧ z = w.next + 2) := by
            intro c' z h
            have h' := (mrg_newKlongs_liveAt_iff false c.i [(0, w.next), (r.1, w.next + 2)] hnd c'
              z).mp h
            simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h'
            exact h'
          obtain ⟨hT', hR'⟩ := treeOK_rootSpaceStep (updN (wNode c.p base w) (X 0)
              (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn 0))) (wNode c.p base w') c.i
            (X 0) w.next (w.next + 2) (w.next + 2 + 2)
            (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn 0))
            out.1 out.2.1 ⟨false, [.time c.i, .key 0 w.next, .key r.1 (w.next + 2)]⟩ r.1
            (splitLocalCv (Nn 0).leaf r.1) hsc hV0 (updN_self _ _ _)
            (by rw [hw']; simp only [hRx, hRF, hRS, ↓reduceIte])
            hrn
            (by rw [hw']; simp only [hFx, ↓reduceIte])
            (by rw [hw']; simp only [hSx, hSF, ↓reduceIte])
            hf hs
            (by
              intro z h1 h2 h3 h4
              rw [hw']
              simp only [h1, h2, h3, h4, ↓reduceIte]
              exact (updN_ne _ _ _ _ h1).symm)
            (by
              intro z hz
              have hzn : w.next ≤ z := by rcases hz with hz | hz | hz <;> omega
              exact ⟨hVnone z hzn, hVfresh z hzn⟩)
            (by omega) (by omega) (by omega)
          have hVR' := rangeOrder_rootSpaceStep (updN (wNode c.p base w) (X 0)
              (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn 0))) (wNode c.p base w') c.i
            (X 0) w.next (w.next + 2) (w.next + 2 + 2)
            (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn 0))
            out.1 out.2.1 ⟨false, [.time c.i, .key 0 w.next, .key r.1 (w.next + 2)]⟩ r.1 hVR0 hV0
            (updN_self _ _ _)
            (Or.inr ⟨hVnone w.next (Nat.le_refl _), hVfresh w.next (Nat.le_refl _)⟩)
            (hVnone (w.next + 2) (by omega)) (hVfresh (w.next + 2) (by omega))
            (hVnone (w.next + 2 + 2) (by omega)) (hVfresh (w.next + 2 + 2) (by omega))
            (by omega) (by omega) (by omega)
            hscL hsc
            (by rw [hw']; simp only [hRx, hRF, hRS, ↓reduceIte]) rfl hrn
            ((mrg_newKlongs_liveAt_iff false c.i [(0, w.next), (r.1, w.next + 2)] hnd r.1
              (w.next + 2)).mpr (by simp))
            (by rw [hw']; simp only [hFx, ↓reduceIte])
            (by
              have := (halves_leaf_flags (Nn 0).leaf c.i ((Nn 0).lastVersion c.i) ins).1
              rw [hout] at this
              rw [this, KNode.addKeys_leaf])
            (fun c' z h => ⟨(hf c' z h).2, (hf c' z h).1⟩)
            (by rw [hw']; simp only [hSx, hSF, ↓reduceIte])
            (by
              have := (halves_leaf_flags (Nn 0).leaf c.i ((Nn 0).lastVersion c.i) ins).2
              rw [hout] at this
              rw [this, KNode.addKeys_leaf])
            (by
              intro c' z h
              obtain ⟨c0, h1, h2, h3⟩ := hs c' z h
              refine ⟨c0, h1, h3, ?_⟩
              rw [h2, splitLocalCv_eq, KNode.addKeys_leaf])
            (by
              intro z h4 h2 h3 h1
              rw [hw']
              simp only [h1, h2, h3, h4, ↓reduceIte]
              exact (updN_ne _ _ _ _ h1).symm)
          refine ⟨by rw [h'root]; exact hT', ⟨Or.inr ⟨rfl, by omega⟩, h't, h'path, by omega, h'v⟩,
            ?_, ?_, by rw [h'root]; exact hVR'⟩
          · intro z hz hzX
            rw [h'n]
            have h1' : ¬ z = X 0 := hzX 0 (Nat.le_refl _) (Nat.le_refl _)
            have h2' : ¬ z = w.next := by omega
            have h3' : ¬ z = w.next + 2 := by omega
            have h4' : ¬ z = w.next + 2 + 2 := by omega
            simp only [h1', h2', h3', h4', ↓reduceIte]
          · intro z hz
            rw [h'root] at hz
            rcases (hR' z hz).1 with h | h | h | h
            · exact Or.inl (by rw [hrk]; exact h)
            · exact Or.inr (by omega)
            · exact Or.inr (by omega)
            · exact Or.inr (by omega)
      rw [appendKlongs_step_dead]
      simp only [writerWP_bind, writerWP_read]
      rw [writerWP_getNode_known _ _ c w hlk]
      by_cases hsz : (Nn 0).size + ins.length + 1 > c.p.M
      · simp only [hsz, ↓reduceIte]
        by_cases hsp : c.p.splitAbove < ((Nn 0).lastVersion c.i).size
        · refine writerWP_mono (hSPACE0 _ hsp) ?_
          intro _ w' h
          simpa using h
        · refine writerWP_mono (hTIME0 _ false (by
            simp only [Bool.not_false, Bool.true_and, decide_eq_false_iff_not, gt_iff_lt]
            exact hsp)) ?_
          intro _ w' h
          simpa using h
      · have hd : deadOver c.p (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn 0)) = true := by
          cases h : deadOver c.p (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn 0)) with
          | true => rfl
          | false => exact absurd ⟨by omega, h⟩ hroom
        simp only [hsz, hd, ↓reduceIte]
        refine writerWP_mono (hTIME0 _ true (by simp)) ?_
        intro _ w' h
        simpa using h
  | succ e ih =>
    intro hD w ins hins hinsT hS1 hS2 hS3 hS4 hS5 hS6 hR0 hV hVR
    have hj : s < s + (e + 1) := by omega
    obtain ⟨hlk, htk⟩ := hS2 (s + (e + 1)) (by omega) (Nat.le_refl _)
    obtain ⟨hlq, htq⟩ := hS2 (s + e) (by omega) (by omega)
    by_cases hroom : (Nn (s + (e + 1))).size + ins.length + 1 ≤ c.p.M ∧
        deadOver c.p (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + (e + 1)))) = false
    · exact hroomCase (e + 1) hD w ins hlk htk hroom.1 hroom.2 hV hVR
    · -- common facts of a split
      have hNR : ¬ ChainRoom c (Nn (s + (e + 1))) := fun ⟨h1, h2⟩ =>
        hroom ⟨by have := hins.length; omega, h2 ins hins.length⟩
      have hpq : (w.path[s + e]?).map (·.2) = some (X (s + e)) := by
        rw [hS1]; exact hX (s + e) (by omega) (by omega)
      have hpk : w.path[s + e + 1]? = some (some (K (s + (e + 1))), X (s + (e + 1))) := by
        rw [hS1]; exact hK (s + (e + 1)) hj hD
      have hkl : (K (s + (e + 1)), X (s + (e + 1))) ∈ (Nn (s + e)).liveAt c.i := by
        have := hlinkK (s + (e + 1)) hj hD; simpa using this
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
      have hXlt : ∀ i, s ≤ i → i ≤ s + (e + 1) → X i < w.next := by
        intro i h1 h2
        obtain ⟨hl, _⟩ := hS2 i h1 h2
        rcases Nat.lt_or_ge (X i) w.next with hlt | hge
        · exact hlt
        · have := (hS5 (X i) hge).1
          rw [hl] at this; cases this
      have hqx : X (s + e) ≠ X (s + (e + 1)) := by
        intro h; have := hdist _ _ (by omega) (by omega) (by omega) hD h; omega
      have hwq : wNode c.p base w (X (s + e)) = some (Nn (s + e)) := by
        simp only [wNode, htq, Bool.false_eq_true, ↓reduceIte, hlq]
      have hwx : wNode c.p base w (X (s + (e + 1))) = some (Nn (s + (e + 1))) := by
        simp only [wNode, htk, Bool.false_eq_true, ↓reduceIte, hlk]
      have hqR : TReach (updN (wNode c.p base w) (X (s + (e + 1)))
          (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + (e + 1))))) c.i w.top.rootKey
          (X (s + e)) :=
        tReach_updN_parent _ c.i _ _ _ _ _ hS3 (hS4 (s + e) (by omega) (by omega))
          ⟨Nn (s + e), hwq, hkl⟩
      have hqtimes := htimes (s + e) (by omega) (by omega)
      have hqwf := hwf (s + e) (by omega) (by omega)
      have hxtimes := htimes (s + (e + 1)) (by omega) hD
      have hxwf := hwf (s + (e + 1)) (by omega) hD
      -- the links of the node with the klongs put are below the next id
      have hvxLinks : ∀ c' z, (c', z) ∈ (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y))
          (Nn (s + (e + 1)))).liveAt c.i → z < w.next := by
        intro c' z h
        have hf := KNode.addKeys_liveAt_fold c.i ins _ hxwf hxtimes c' z h
        rcases pairLookupFold_some_mem c' ins _ z hf with hm | hm
        · exact hinsT (c', z) hm
        · have hm' := lookup_some_mem hm
          rw [← KNode.liveAt_of_times _ c.i hxtimes] at hm'
          exact hS6 _ _ _ ⟨_, hwx, hm'⟩
      have hVfresh : ∀ z, w.next ≤ z → ∀ u c', TReach (updN (wNode c.p base w) (X (s + (e + 1)))
          (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + (e + 1))))) c.i w.top.rootKey u →
          ¬ TLink (updN (wNode c.p base w) (X (s + (e + 1)))
            (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + (e + 1))))) c.i u c' z := by
        intro z hz u c' _ hl
        obtain ⟨m, hm, hc⟩ := hl
        by_cases hu : u = X (s + (e + 1))
        · rw [hu, updN_self] at hm
          simp only [Option.some.injEq] at hm
          subst hm
          have := hvxLinks c' z hc; omega
        · rw [updN_ne _ _ _ _ hu] at hm
          exact hnoLink z hz u c' ⟨m, hm, hc⟩
      -- the rest of a split: the parent's step by the induction, then the node left behind
      have hfinish : ∀ (w1 : W) (ins' : List (Nat × NodeId)) (N1 : NodeId → Option KNode)
          (New : NodeId → Prop),
          InsOK (Nn (s + e)) ins' → (∀ q ∈ ins', q.2 < w1.next) →
          w1.path = w.path → w1.taken = w.taken → w1.top = w.top → w.next + 2 ≤ w1.next →
          w1.vals = w.vals → (∀ z, New z → w.next ≤ z) →
          (∀ z, z < w.next → w1.nodes.lookup z = w.nodes.lookup z) →
          wNode c.p base w1 = N1 →
          TreeOK N1 c.i w.top.rootKey →
          (∀ i, s ≤ i → i ≤ s + e → TReach N1 c.i w.top.rootKey (X i)) →
          (∀ z, w1.next ≤ z → w1.nodes.lookup z = none ∧ w1.taken.contains z = false ∧
            knodeOf c.p base z = none) →
          (∀ u c' z, TLink N1 c.i u c' z → z < w1.next) →
          TreeOK (updN N1 (X (s + e)) (ins'.foldl (fun n (cv, y) => n.add c.i (.key cv y))
            (Nn (s + e)))) c.i w.top.rootKey →
          RangeOrder (updN N1 (X (s + e)) (ins'.foldl (fun n (cv, y) => n.add c.i (.key cv y))
            (Nn (s + e)))) c.i w.top.rootKey →
          (∀ z, TReach (updN N1 (X (s + e)) (ins'.foldl (fun n (cv, y) => n.add c.i (.key cv y))
            (Nn (s + e)))) c.i w.top.rootKey z →
            (TReach (updN (wNode c.p base w) (X (s + (e + 1)))
              (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + (e + 1))))) c.i
              w.top.rootKey z ∨ New z) ∧ z ≠ X (s + (e + 1))) →
          WriterWP (appendKlongs (s + e) (X (s + e)) ins') c w1 (fun _ w2 =>
            WriterWP (do let m ← getNode (X (s + (e + 1))); putNode (X (s + (e + 1))) (m.toPrev (c.i - 1)))
              c w2 (fun _ w3 =>
              TreeOK (wNode c.p base w3) c.i w3.top.rootKey ∧
              ((w3.top = w.top ∨ (s = 0 ∧ w.next ≤ w3.top.rootKey)) ∧ w3.taken = w.taken ∧ w3.path = w.path ∧ w.next ≤ w3.next ∧ w3.vals = w.vals) ∧
              (∀ z, z < w.next → (∀ i, s ≤ i → i ≤ s + (e + 1) → z ≠ X i) →
                w3.nodes.lookup z = w.nodes.lookup z) ∧
              (∀ z, TReach (wNode c.p base w3) c.i w3.top.rootKey z →
                TReach (updN (wNode c.p base w) (X (s + (e + 1)))
                  (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + (e + 1))))) c.i
                  w.top.rootKey z ∨ w.next ≤ z) ∧
              RangeOrder (wNode c.p base w3) c.i w3.top.rootKey)) := by
        intro w1 ins' N1 New hins' hinsT' h1path h1t h1top h1next h1vals hNew h1low hN1 hT1 hR1 hS5' hS6' hV1 hVR1 hRV1
        have hpar := ih (by omega) w1 ins' hins' hinsT' (by rw [h1path, hS1])
          (by
            intro i h1 h2
            obtain ⟨a, b⟩ := hS2 i h1 (by omega)
            refine ⟨?_, by rw [h1t]; exact b⟩
            rw [h1low _ (hXlt i h1 (by omega)), a])
          (by rw [hN1, h1top]; exact hT1)
          (by intro i h1 h2; rw [hN1, h1top]; exact hR1 i h1 h2)
          hS5' (by rw [hN1]; exact hS6') (fun h0 => by rw [h1top]; exact hR0 h0)
          (by rw [hN1, h1top]; exact hV1)
          (by rw [hN1, h1top]; exact hVR1)
        refine writerWP_mono hpar ?_
        rintro _ w2 ⟨hT2, ⟨h2top, h2t, h2path, h2next, h2vals⟩, h2frame, h2reach, h2R⟩
        have hlk2 : w2.nodes.lookup (X (s + (e + 1))) = some (Nn (s + (e + 1))) := by
          rw [h2frame _ (by have := hXlt (s + (e + 1)) (by omega) (Nat.le_refl _); omega)
            (fun i h1 h2 he => by have := hdist _ _ (by omega) hD h1 (by omega) he; omega),
            h1low _ (hXlt (s + (e + 1)) (by omega) (Nat.le_refl _)), hlk]
        simp only [writerWP_bind]
        rw [writerWP_getNode_known _ _ c w2 hlk2]
        simp only [putNode, writerWP_modify]
        have htk2 : w2.taken.contains (X (s + (e + 1))) = false := by rw [h2t, h1t]; exact htk
        generalize hw3 : ({ w2 with nodes := upsert w2.nodes (X (s + (e + 1))) ((Nn (s + (e + 1))).toPrev (c.i - 1)) } : W) = w3
        have h3n : w3.nodes = upsert w2.nodes (X (s + (e + 1))) ((Nn (s + (e + 1))).toPrev (c.i - 1)) := by
          rw [← hw3]
        have h3t : w3.taken = w2.taken := by rw [← hw3]
        have hN3 := wNode_upsert_updN c.p base w2 w3 (X (s + (e + 1))) _ h3n h3t htk2
        have hxR2 : ¬ TReach (wNode c.p base w2) c.i w2.top.rootKey (X (s + (e + 1))) := by
          intro h
          rcases h2reach _ h with h' | h'
          · rw [hN1, h1top] at h'
            exact (hRV1 _ h').2 rfl
          · have := hXlt (s + (e + 1)) (by omega) (Nat.le_refl _); omega
        refine ⟨?_, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
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
            · exact Or.inl h''
            · exact Or.inr (hNew z h'')
          · exact Or.inr (by omega)
        · rw [hN3]
          refine rangeOrder_agree _ _ c.i _ h2R ?_
          intro z hz
          exact updN_ne _ _ _ _ (fun h => hxR2 (h ▸ hz))
      have hanc : ∀ m : KNode, ∀ i, s ≤ i → i ≤ s + e →
          TReach (updN (wNode c.p base w) (X (s + (e + 1))) m) c.i w.top.rootKey (X i) :=
        fun m i h1 h2 => chain_anc_reach (wNode c.p base w) c.i w.top.rootKey X s (s + (e + 1)) hS3
          (hS4 s (Nat.le_refl _) (by omega))
          (fun i' h1' h2' => by
            obtain ⟨a, b⟩ := hS2 (i' - 1) (by omega) (by omega)
            exact ⟨K i', Nn (i' - 1), by simp only [wNode, b, Bool.false_eq_true, ↓reduceIte, a],
              hlinkK i' h1' (by omega)⟩) m i h1 (by omega)
      -- a time split, for either flag
      have hstepT : (Nn (s + (e + 1))).firstTime ≠ some c.i → ∀ compact : Bool,
          (!compact && decide (((Nn (s + (e + 1))).lastVersion c.i).size > c.p.splitAbove)) = false →
          WriterWP (handleFullWith (fun q more => appendKlongs (s + e) q more) (s + e + 1)
            (X (s + (e + 1))) ins ((Nn (s + (e + 1))).lastVersion c.i) compact) c w (fun _ w' =>
            TreeOK (wNode c.p base w') c.i w'.top.rootKey ∧
            ((w'.top = w.top ∨ (s = 0 ∧ w.next ≤ w'.top.rootKey)) ∧ w'.taken = w.taken ∧ w'.path = w.path ∧ w.next ≤ w'.next ∧ w'.vals = w.vals) ∧
            (∀ z, z < w.next → (∀ i, s ≤ i → i ≤ s + (e + 1) → z ≠ X i) →
              w'.nodes.lookup z = w.nodes.lookup z) ∧
            (∀ z, TReach (wNode c.p base w') c.i w'.top.rootKey z →
              TReach (updN (wNode c.p base w) (X (s + (e + 1)))
                (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + (e + 1))))) c.i
                w.top.rootKey z ∨ w.next ≤ z) ∧
            RangeOrder (wNode c.p base w') c.i w'.top.rootKey) := by
        intro hfirst compact hcs
        apply writerWP_handleFullWith_time_up' (s + e) (X (s + (e + 1))) (X (s + e)) (Nn (s + (e + 1)))
          (Nn (s + e)) (K (s + (e + 1))) ins compact c w hlk hlq hfirst hcs hpq hpk
        intro l hl_leaf hl_wf hl_times hl_look w1 h1n h1t h1top h1path h1next h1vals
        have hN1 : wNode c.p base w1 = updN (wNode c.p base w) w.next ⟨(Nn (s + (e + 1))).leaf, l.ks⟩ :=
          wNode_append_updN c.p base w w1 _ h1n h1t hfree0 htk0
        have hlsub : ∀ c' z, (c', z) ∈ (⟨(Nn (s + (e + 1))).leaf, l.ks⟩ : KNode).liveAt c.i →
            (c', z) ∈ (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + (e + 1)))).liveAt c.i := by
          intro c' z h
          apply KNode.addKeys_liveAt_of_fold c.i ins _ hxwf hxtimes
          have h' : (c', z) ∈ (⟨(Nn (s + (e + 1))).leaf, l.ks⟩ : KNode).live := by
            rw [← KNode.liveAt_of_times (⟨(Nn (s + (e + 1))).leaf, l.ks⟩ : KNode) c.i hl_times]; exact h
          have hlk' := lookup_of_mem_nodup _ (KNode.live_keys_nodup _) c' z h'
          rw [← hl_look c']
          exact hlk'
        obtain ⟨hT1V, hR1V⟩ := treeOK_timeSplit_gen (updN (wNode c.p base w) (X (s + (e + 1)))
            (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + (e + 1)))))
          (updN (wNode c.p base w1) (X (s + e)) ([(K (s + (e + 1)), w.next)].foldl
            (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + e)))) c.i w.top.rootKey (X (s + e))
          (X (s + (e + 1))) w.next (Nn (s + e))
          (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + (e + 1))))
          ⟨(Nn (s + (e + 1))).leaf, l.ks⟩
          ([(K (s + (e + 1)), w.next)].foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + e)))
          (K (s + (e + 1))) hV hqR (by rw [updN_ne _ _ _ _ hqx]; exact hwq)
          hkl (updN_self _ _ _) (updN_self _ _ _)
          (fun c' z h => KNode.add_key_liveAt_mem _ c.i _ _ hqwf hqtimes c' z h)
          (by
            rw [updN_ne _ _ _ _ (fun h => by have := hXlt (s + e) (by omega) (by omega); omega), hN1]
            exact updN_self _ _ _)
          hlsub
          (by
            intro z hz1 hz2 hz3
            rw [updN_ne _ _ _ _ hz2, hN1, updN_ne _ _ _ _ hz3]
            exact (updN_ne _ _ _ _ hz1).symm)
          (by
            rw [updN_ne _ _ _ _ (fun h => by
              have := hXlt (s + (e + 1)) (by omega) (Nat.le_refl _); omega)]
            exact hwnext)
          (hVfresh w.next (Nat.le_refl _))
        have hVR1 := rangeOrder_timeStepAny (updN (wNode c.p base w) (X (s + (e + 1)))
            (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + (e + 1)))))
          (updN (wNode c.p base w1) (X (s + e)) ([(K (s + (e + 1)), w.next)].foldl
            (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + e)))) c.i w.top.rootKey hVR hV
          (X (s + e)) (X (s + (e + 1))) w.next (Nn (s + e))
          (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + (e + 1))))
          ⟨(Nn (s + (e + 1))).leaf, l.ks⟩
          ([(K (s + (e + 1)), w.next)].foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + e)))
          (K (s + (e + 1))) hqR (by rw [updN_ne _ _ _ _ hqx]; exact hwq) hkl (updN_self _ _ _)
          (by
            rw [updN_ne _ _ _ _ (fun h => by
              have := hXlt (s + (e + 1)) (by omega) (Nat.le_refl _); omega)]
            exact hwnext)
          (hVfresh w.next (Nat.le_refl _)) (updN_self _ _ _)
          (by simp only [List.foldl_cons, List.foldl_nil, KNode.add_leaf])
          (fun c' z h => KNode.add_key_liveAt_mem _ c.i _ _ hqwf hqtimes c' z h)
          (by
            rw [updN_ne _ _ _ _ (fun h => by have := hXlt (s + e) (by omega) (by omega); omega), hN1]
            exact updN_self _ _ _)
          (KNode.addKeys_leaf c.i ins (Nn (s + (e + 1)))).symm hlsub
          (by
            intro z hz1 hz2 hz3
            rw [updN_ne _ _ _ _ hz1, hN1, updN_ne _ _ _ _ hz2]
            exact (updN_ne _ _ _ _ hz3).symm)
        apply hfinish w1 [(K (s + (e + 1)), w.next)] _ (fun z => z = w.next)
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
          (by rw [← hN1]; exact hVR1)
          (by rw [← hN1]; exact hR1V)
      -- a space split
      have hstepS : (Nn (s + (e + 1))).firstTime ≠ some c.i → (Nn (s + e)).leaf = false →
          c.p.splitAbove < ((Nn (s + (e + 1))).lastVersion c.i).size →
          WriterWP (handleFullWith (fun q more => appendKlongs (s + e) q more) (s + e + 1)
            (X (s + (e + 1))) ins ((Nn (s + (e + 1))).lastVersion c.i) false) c w (fun _ w' =>
            TreeOK (wNode c.p base w') c.i w'.top.rootKey ∧
            ((w'.top = w.top ∨ (s = 0 ∧ w.next ≤ w'.top.rootKey)) ∧ w'.taken = w.taken ∧ w'.path = w.path ∧ w.next ≤ w'.next ∧ w'.vals = w.vals) ∧
            (∀ z, z < w.next → (∀ i, s ≤ i → i ≤ s + (e + 1) → z ≠ X i) →
              w'.nodes.lookup z = w.nodes.lookup z) ∧
            (∀ z, TReach (wNode c.p base w') c.i w'.top.rootKey z →
              TReach (updN (wNode c.p base w) (X (s + (e + 1)))
                (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + (e + 1))))) c.i
                w.top.rootKey z ∨ w.next ≤ z) ∧
            RangeOrder (wNode c.p base w') c.i w'.top.rootKey) := by
        intro hfirst hql hsp
        have h2l := hlen (s + (e + 1)) (by omega) hD hNR hsp
        obtain ⟨r, hr⟩ := divider_exists (Nn (s + (e + 1))) (by omega)
        have hrm := divider_mem_live _ r hr
        have hsc := divider_pos' _ r h2l hr
        obtain ⟨a, more, hins_eq, hside⟩ := hins.side r hrm
        obtain ⟨hdiv, hfh, hsh⟩ := halves_links (Nn (s + (e + 1))).leaf c.i (Nn (s + (e + 1))) rfl
          a more r hr hsc hside
        rw [← hins_eq] at hdiv hfh hsh
        apply writerWP_handleFullWith_space_up (s + e) (X (s + (e + 1))) (X (s + e)) (Nn (s + (e + 1)))
          (Nn (s + e)) (K (s + (e + 1))) ins c w hlk hlq hql hfirst hsp hpq hpk
        intro w1 h1n h1t h1top h1path h1next h1vals
        obtain ⟨out, hout⟩ : ∃ o, halves (Nn (s + (e + 1))).leaf c.i ((Nn (s + (e + 1))).lastVersion c.i) ins = o :=
          ⟨_, rfl⟩
        rw [hout] at h1n hdiv hfh hsh ⊢
        rw [hdiv]
        have h12 : w.next ≠ w.next + 2 := by omega
        have hN1 : wNode c.p base w1 = updN (updN (wNode c.p base w) w.next out.1) (w.next + 2) out.2.1 :=
          wNode_two_updN c.p base w w1 _ _ _ _ h1n h1t h12 htk0 htk2'
        have hf : ∀ c' z, (c', z) ∈ out.1.liveAt c.i → c' < r.1 ∧
            (c', z) ∈ (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + (e + 1)))).liveAt c.i := by
          intro c' z h
          obtain ⟨h1, h2⟩ := hfh c' z h
          exact ⟨h1, KNode.addKeys_liveAt_of_fold c.i ins _ hxwf hxtimes c' z h2⟩
        have hs : ∀ c' z, (c', z) ∈ out.2.1.liveAt c.i → ∃ c0, r.1 ≤ c0 ∧
            c' = splitLocalCv (Nn (s + (e + 1))).leaf r.1 c0 ∧
            (c0, z) ∈ (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + (e + 1)))).liveAt c.i := by
          intro c' z h
          obtain ⟨c0, h1, h2, h3⟩ := hsh c' z h
          exact ⟨c0, h1, h2, KNode.addKeys_liveAt_of_fold c.i ins _ hxwf hxtimes c0 z h3⟩
        have hq1wf := KNode.add_key_wf (Nn (s + e)) c.i (K (s + (e + 1))) w.next hqwf
        have hq1t := KNode.add_times (Nn (s + e)) c.i (.key (K (s + (e + 1))) w.next)
          (fun s h => by cases h) hqtimes
        have hqlinks : ∀ c' z, (c', z) ∈ ([(K (s + (e + 1)), w.next), (r.1, w.next + 2)].foldl
            (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + e))).liveAt c.i →
            (c' = r.1 ∧ z = w.next + 2) ∨ (c' ≠ r.1 ∧ c' = K (s + (e + 1)) ∧ z = w.next) ∨
            (c' ≠ r.1 ∧ c' ≠ K (s + (e + 1)) ∧ (c', z) ∈ (Nn (s + e)).liveAt c.i) := by
          intro c' z h
          simp only [List.foldl_cons, List.foldl_nil] at h
          rcases KNode.add_key_liveAt_mem _ c.i _ _ hq1wf hq1t c' z h with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact Or.inl ⟨h1, h2⟩
          · rcases KNode.add_key_liveAt_mem _ c.i _ _ hqwf hqtimes c' z h2 with ⟨h3, h4⟩ | ⟨h3, h4⟩
            · exact Or.inr (Or.inl ⟨h1, h3, h4⟩)
            · exact Or.inr (Or.inr ⟨h1, h3, h4⟩)
        have hXn1 : X (s + (e + 1)) ≠ w.next := by
          have := hXlt (s + (e + 1)) (by omega) (Nat.le_refl _); omega
        have hXn2 : X (s + (e + 1)) ≠ w.next + 2 := by
          have := hXlt (s + (e + 1)) (by omega) (Nat.le_refl _); omega
        have hQn1 : X (s + e) ≠ w.next := by have := hXlt (s + e) (by omega) (by omega); omega
        have hQn2 : X (s + e) ≠ w.next + 2 := by have := hXlt (s + e) (by omega) (by omega); omega
        obtain ⟨hT1V, hR1V⟩ := treeOK_spaceSplit_gen (updN (wNode c.p base w) (X (s + (e + 1)))
            (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + (e + 1)))))
          (updN (wNode c.p base w1) (X (s + e)) ([(K (s + (e + 1)), w.next), (r.1, w.next + 2)].foldl
            (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + e)))) c.i w.top.rootKey (X (s + e))
          (X (s + (e + 1))) w.next (w.next + 2) (Nn (s + e))
          (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + (e + 1)))) out.1 out.2.1
          ([(K (s + (e + 1)), w.next), (r.1, w.next + 2)].foldl
            (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + e)))
          (K (s + (e + 1))) r.1 (splitLocalCv (Nn (s + (e + 1))).leaf r.1) hV hqR
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
        have hrK := hrange (s + (e + 1)) hj hD hNR (by simpa using hql) r.1 r.2 hrm hsc
        -- a compare value of the node is one of the node with the klongs put
        have hcvV : ∀ c' z, (c', z) ∈ (Nn (s + (e + 1))).live → ∃ z',
            (c', z') ∈ (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + (e + 1)))).liveAt c.i := by
          intro c' z h
          have hl0 := lookup_of_mem_nodup _ (KNode.live_keys_nodup _) c' z h
          obtain ⟨z', hz'⟩ := pairLookupFold_isSome c' ins ((Nn (s + (e + 1))).live.lookup c')
            (by rw [hl0]; rfl)
          exact ⟨z', KNode.addKeys_liveAt_of_fold c.i ins _ hxwf hxtimes c' z' hz'⟩
        obtain ⟨a0, ha0, ha0r⟩ := live_below_divider (Nn (s + (e + 1))) r h2l hr
        have hVR1 := rangeOrder_spaceStep (updN (wNode c.p base w) (X (s + (e + 1)))
            (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + (e + 1)))))
          (updN (wNode c.p base w1) (X (s + e)) ([(K (s + (e + 1)), w.next), (r.1, w.next + 2)].foldl
            (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + e)))) c.i w.top.rootKey hVR hV
          (X (s + e)) (X (s + (e + 1))) w.next (w.next + 2) (Nn (s + e))
          (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + (e + 1)))) out.1 out.2.1
          ([(K (s + (e + 1)), w.next), (r.1, w.next + 2)].foldl
            (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + e)))
          (K (s + (e + 1))) r.1 hqR (by rw [updN_ne _ _ _ _ hqx]; exact hwq) hql hkl (updN_self _ _ _)
          (by rw [updN_ne _ _ _ _ hXn1.symm]; exact hwnext)
          (by rw [updN_ne _ _ _ _ hXn2.symm]; exact hwnext2) h12
          (hVfresh w.next (Nat.le_refl _)) (hVfresh (w.next + 2) (by omega))
          (hcvV r.1 r.2 hrm) (by
            obtain ⟨z', hz'⟩ := hcvV a0.1 a0.2 ha0
            exact ⟨a0.1, z', hz', ha0r⟩)
          (updN_self _ _ _)
          (by simp only [List.foldl_cons, List.foldl_nil, KNode.add_leaf]; exact hql)
          (by
            intro c' z h
            rcases hqlinks c' z h with h1 | ⟨_, h1⟩ | ⟨_, h1⟩
            · exact Or.inl h1
            · exact Or.inr (Or.inl h1)
            · exact Or.inr (Or.inr h1))
          (KNode.addKeys_liveAt_of_fold c.i _ _ hqwf hqtimes _ _ (by simp [pairLookupStep]))
          (by rw [updN_ne _ _ _ _ hQn1.symm, hN1, updN_ne _ _ _ _ h12]; exact updN_self _ _ _)
          (by
            have := (halves_leaf_flags (Nn (s + (e + 1))).leaf c.i ((Nn (s + (e + 1))).lastVersion c.i) ins).1
            rw [hout] at this
            rw [this, KNode.addKeys_leaf])
          (fun c' z h => ⟨(hf c' z h).2, (hf c' z h).1⟩)
          (by rw [updN_ne _ _ _ _ hQn2.symm, hN1]; exact updN_self _ _ _)
          (by
            have := (halves_leaf_flags (Nn (s + (e + 1))).leaf c.i ((Nn (s + (e + 1))).lastVersion c.i) ins).2
            rw [hout] at this
            rw [this, KNode.addKeys_leaf])
          (by
            intro c' z h
            obtain ⟨c0, h1, h2, h3⟩ := hs c' z h
            refine ⟨c0, h1, h3, ?_⟩
            rw [h2, splitLocalCv_eq, KNode.addKeys_leaf])
          (by
            intro z hz1 hz2 hz3 hz4
            rw [updN_ne _ _ _ _ hz1, hN1, updN_ne _ _ _ _ hz3, updN_ne _ _ _ _ hz2]
            exact (updN_ne _ _ _ _ hz4).symm)
        apply hfinish w1 [(K (s + (e + 1)), w.next), (r.1, w.next + 2)] _
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
          (by rw [← hN1]; exact hVR1)
          (by rw [← hN1]; exact hR1V)
      -- the time split, made by the transaction or not
      have hTIME : ∀ compact : Bool,
          (!compact && decide (((Nn (s + (e + 1))).lastVersion c.i).size > c.p.splitAbove)) = false →
          WriterWP (handleFullWith (fun q more => appendKlongs (s + e) q more) (s + e + 1)
            (X (s + (e + 1))) ins ((Nn (s + (e + 1))).lastVersion c.i) compact) c w (fun _ w' =>
            TreeOK (wNode c.p base w') c.i w'.top.rootKey ∧
            ((w'.top = w.top ∨ (s = 0 ∧ w.next ≤ w'.top.rootKey)) ∧ w'.taken = w.taken ∧
              w'.path = w.path ∧ w.next ≤ w'.next ∧ w'.vals = w.vals) ∧
            (∀ z, z < w.next → (∀ i, s ≤ i → i ≤ s + (e + 1) → z ≠ X i) →
              w'.nodes.lookup z = w.nodes.lookup z) ∧
            (∀ z, TReach (wNode c.p base w') c.i w'.top.rootKey z →
              TReach (updN (wNode c.p base w) (X (s + (e + 1)))
                (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + (e + 1))))) c.i
                w.top.rootKey z ∨ w.next ≤ z) ∧
            RangeOrder (wNode c.p base w') c.i w'.top.rootKey) := by
        intro compact hcs
        by_cases hmade : (Nn (s + (e + 1))).firstTime = some c.i
        · -- a time split in place: the node holds what the tree with the klongs put has
          refine writerWP_mono (writerWP_handleFullWith_timeInPlace_term _ (s + e) (X (s + (e + 1)))
            (X (s + e)) (Nn (s + (e + 1))) (Nn (s + e)) ins compact c w hlk hlq hpq hmade hcs) ?_
          rintro _ w' ⟨l, hl_leaf, hl_wf, hl_times, hl_look, h't, h'top, h'v, h'next, h'path, h'n⟩
          have hN' : wNode c.p base w' = updN (wNode c.p base w) (X (s + (e + 1)))
              ⟨(Nn (s + (e + 1))).leaf, l.ks⟩ := wNode_upsert_updN c.p base w w' _ _ h'n h't htk
          have hlsub : ∀ c' z, (c', z) ∈ (⟨(Nn (s + (e + 1))).leaf, l.ks⟩ : KNode).liveAt c.i →
              (c', z) ∈ (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + (e + 1)))).liveAt
                c.i := by
            intro c' z h
            apply KNode.addKeys_liveAt_of_fold c.i ins _ hxwf hxtimes
            have h' : (c', z) ∈ (⟨(Nn (s + (e + 1))).leaf, l.ks⟩ : KNode).live := by
              rw [← KNode.liveAt_of_times (⟨(Nn (s + (e + 1))).leaf, l.ks⟩ : KNode) c.i hl_times]; exact h
            have hlk' := lookup_of_mem_nodup _ (KNode.live_keys_nodup _) c' z h'
            rw [← hl_look c']
            exact hlk'
          obtain ⟨hT', hR'⟩ := treeOK_updN_sub (wNode c.p base w) c.i w.top.rootKey (X (s + (e + 1))) _
            _ hV hlsub
          have hVR' := rangeOrder_updN_sub (wNode c.p base w) c.i w.top.rootKey (X (s + (e + 1))) _
            ⟨(Nn (s + (e + 1))).leaf, l.ks⟩ hVR (KNode.addKeys_leaf c.i ins (Nn (s + (e + 1)))).symm hlsub
          refine ⟨by rw [hN', h'top]; exact hT', ⟨Or.inl h'top, h't, h'path, by omega, h'v⟩, ?_, ?_,
            by rw [hN', h'top]; exact hVR'⟩
          · intro z _ hzX
            rw [h'n, lookup_upsert, ite_eq_right_of_eq_false _ _ (eq_false (hzX _ (by omega) (Nat.le_refl _)))]
          · intro z hz
            rw [hN', h'top] at hz
            exact Or.inl (hR' z hz)
        · exact hstepT hmade compact hcs
      -- the space split, made by the transaction or not, below an inner node or a leaf
      have hSPACE : c.p.splitAbove < ((Nn (s + (e + 1))).lastVersion c.i).size →
          WriterWP (handleFullWith (fun q more => appendKlongs (s + e) q more) (s + e + 1)
            (X (s + (e + 1))) ins ((Nn (s + (e + 1))).lastVersion c.i) false) c w (fun _ w' =>
            TreeOK (wNode c.p base w') c.i w'.top.rootKey ∧
            ((w'.top = w.top ∨ (s = 0 ∧ w.next ≤ w'.top.rootKey)) ∧ w'.taken = w.taken ∧
              w'.path = w.path ∧ w.next ≤ w'.next ∧ w'.vals = w.vals) ∧
            (∀ z, z < w.next → (∀ i, s ≤ i → i ≤ s + (e + 1) → z ≠ X i) →
              w'.nodes.lookup z = w.nodes.lookup z) ∧
            (∀ z, TReach (wNode c.p base w') c.i w'.top.rootKey z →
              TReach (updN (wNode c.p base w) (X (s + (e + 1)))
                (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + (e + 1))))) c.i
                w.top.rootKey z ∨ w.next ≤ z) ∧
            RangeOrder (wNode c.p base w') c.i w'.top.rootKey) := by
        intro hsp
        by_cases hmade : (Nn (s + (e + 1))).firstTime = some c.i
        · by_cases hqlf : (Nn (s + e)).leaf = true
          · -- a space split in place below a leaf: a new inner node above, the leaf repointed
            have h2l := hlen (s + (e + 1)) (by omega) hD hNR hsp
            obtain ⟨r, hdiv, hsc, hscL, hlowL, hf, hs⟩ := chain_halves_factsR c.i (Nn (s + (e + 1))) ins
              hins h2l hxtimes hxwf
            have hXj := hXlt (s + (e + 1)) (by omega) (Nat.le_refl _)
            have hXq := hXlt (s + e) (by omega) (by omega)
            refine writerWP_mono (writerWP_handleFullWith_segSpaceInPlace_term (s + e) (X (s + (e + 1)))
              (X (s + e)) (Nn (s + (e + 1))) (Nn (s + e)) (K (s + (e + 1))) ins c w hlk hlq hqx hqlf
              hmade hsp hpq hpk hXj hXq hfree2) ?_
            rintro _ w' ⟨j0, hj0, h't, h'top, h'v, h'path, h'next, h'n⟩
            obtain ⟨out, hout⟩ : ∃ o, halves (Nn (s + (e + 1))).leaf c.i
                ((Nn (s + (e + 1))).lastVersion c.i) ins = o := ⟨_, rfl⟩
            rw [hout] at h'n hdiv hf hs
            rw [hdiv] at h'n
            obtain ⟨hq2k, hq2⟩ := KNode.repoint_link_facts (Nn (s + e)) c.i (X (s + (e + 1)))
              (w.next + 2) (K (s + (e + 1))) j0 hj0 hqtimes
            have hjF : ¬ X (s + (e + 1)) = w.next := by omega
            have hjR : ¬ X (s + (e + 1)) = w.next + 2 := by omega
            have hqF : ¬ X (s + e) = w.next := by omega
            have hqR' : ¬ X (s + e) = w.next + 2 := by omega
            have hFj : ¬ w.next = X (s + (e + 1)) := by omega
            have hRj : ¬ w.next + 2 = X (s + (e + 1)) := by omega
            have hFq : ¬ w.next = X (s + e) := by omega
            have hRq : ¬ w.next + 2 = X (s + e) := by omega
            have hRF : ¬ w.next + 2 = w.next := by omega
            have hw' : ∀ z, wNode c.p base w' z =
                if z = X (s + (e + 1)) then some out.1
                else if z = X (s + e) then some ((Nn (s + e)).repoint j0 (w.next + 2))
                else if z = w.next then some out.2.1
                else if z = w.next + 2 then
                  some ⟨false, [.time c.i, .key 0 (X (s + (e + 1))), .key r.1 w.next]⟩
                else wNode c.p base w z := by
              intro z
              by_cases h1 : z = X (s + (e + 1))
              · subst h1; simp only [wNode, h't, htk, h'n, Bool.false_eq_true, ↓reduceIte]
              · by_cases h2 : z = X (s + e)
                · subst h2; simp only [wNode, h't, htq, h'n, h1, Bool.false_eq_true, ↓reduceIte]
                · by_cases h3 : z = w.next
                  · subst h3
                    simp only [wNode, h't, htk0, h'n, h1, h2, Bool.false_eq_true, ↓reduceIte]
                  · by_cases h4 : z = w.next + 2
                    · subst h4
                      simp only [wNode, h't, htk2', h'n, h1, h2, h3, Bool.false_eq_true, ↓reduceIte]
                    · simp only [wNode, h't, h'n, h1, h2, h3, h4, ↓reduceIte]
            have hnd : ([(0, X (s + (e + 1))), (r.1, w.next)].map Prod.fst).Nodup := by
              simp only [List.map_cons, List.map_nil, List.nodup_cons, List.mem_cons,
                List.not_mem_nil, or_false, List.nodup_nil, and_true, not_false_eq_true]
              omega
            have hrn : ∀ c' z, (c', z) ∈ (⟨false, [.time c.i, .key 0 (X (s + (e + 1))),
                .key r.1 w.next]⟩ : KNode).liveAt c.i →
                (c' = 0 ∧ z = X (s + (e + 1))) ∨ (c' = r.1 ∧ z = w.next) := by
              intro c' z h
              have h' := (mrg_newKlongs_liveAt_iff false c.i [(0, X (s + (e + 1))), (r.1, w.next)]
                hnd c' z).mp h
              simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h'
              exact h'
            obtain ⟨hT2, hR2⟩ := treeOK_segSpaceInPlaceStep
              (updN (wNode c.p base w) (X (s + (e + 1)))
                (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + (e + 1)))))
              (wNode c.p base w') c.i w.top.rootKey (X (s + e)) (X (s + (e + 1))) w.next (w.next + 2)
              (Nn (s + e)) (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + (e + 1))))
              out.1 out.2.1 ⟨false, [.time c.i, .key 0 (X (s + (e + 1))), .key r.1 w.next]⟩
              ((Nn (s + e)).repoint j0 (w.next + 2))
              (K (s + (e + 1))) r.1 (splitLocalCv (Nn (s + (e + 1))).leaf r.1) hsc hV hqR
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
            have hVR2 := rangeOrder_segSpaceStep
              (updN (wNode c.p base w) (X (s + (e + 1)))
                (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + (e + 1)))))
              (wNode c.p base w') c.i w.top.rootKey (X (s + e)) (X (s + (e + 1))) (X (s + (e + 1)))
              w.next (w.next + 2)
              (Nn (s + e)) ((Nn (s + e)).repoint j0 (w.next + 2))
              (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + (e + 1))))
              out.1 out.2.1 ⟨false, [.time c.i, .key 0 (X (s + (e + 1))), .key r.1 w.next]⟩
              (K (s + (e + 1))) r.1 hVR hV hqR
              (by rw [updN_ne _ _ _ _ hqx]; exact hwq) hqlf hkl (updN_self _ _ _)
              (by rw [hw']; simp only [hqx, ↓reduceIte])
              (by rw [KNode.repoint_leaf]; exact hqlf) hq2 (Or.inl rfl)
              (by rw [updN_ne _ _ _ _ (fun h => by omega)]; exact hwnext)
              (hVfresh w.next (Nat.le_refl _))
              (by rw [updN_ne _ _ _ _ (fun h => by omega)]; exact hwnext2)
              (hVfresh (w.next + 2) (by omega))
              hjF hjR (by omega) hscL hsc
              (by rw [hw']; simp only [hRj, hRq, hRF, ↓reduceIte]) rfl hrn
              ((mrg_newKlongs_liveAt_iff false c.i [(0, X (s + (e + 1))), (r.1, w.next)] hnd r.1
                w.next).mpr (by simp))
              (by rw [hw']; simp only [↓reduceIte])
              (by
                have := (halves_leaf_flags (Nn (s + (e + 1))).leaf c.i
                  ((Nn (s + (e + 1))).lastVersion c.i) ins).1
                rw [hout] at this
                rw [this, KNode.addKeys_leaf])
              (fun c' z h => ⟨(hf c' z h).2, (hf c' z h).1⟩)
              (by rw [hw']; simp only [hFj, hFq, ↓reduceIte])
              (by
                have := (halves_leaf_flags (Nn (s + (e + 1))).leaf c.i
                  ((Nn (s + (e + 1))).lastVersion c.i) ins).2
                rw [hout] at this
                rw [this, KNode.addKeys_leaf])
              (by
                intro c' z h
                obtain ⟨c0, h1, h2, h3⟩ := hs c' z h
                refine ⟨c0, h1, h3, ?_⟩
                rw [h2, splitLocalCv_eq, KNode.addKeys_leaf])
              (by
                intro z h2 h4 _ h3 h1
                rw [hw']
                simp only [h1, h2, h3, h4, ↓reduceIte]
                exact (updN_ne _ _ _ _ h1).symm)
            refine ⟨by rw [h'top]; exact hT2, ⟨Or.inl h'top, h't, h'path, by omega, h'v⟩, ?_, ?_,
              by rw [h'top]; exact hVR2⟩
            · intro z hz hzX
              rw [h'n]
              have h1' : ¬ z = X (s + (e + 1)) := hzX _ (by omega) (Nat.le_refl _)
              have h2' : ¬ z = X (s + e) := hzX _ (by omega) (by omega)
              have h3' : ¬ z = w.next := by omega
              have h4' : ¬ z = w.next + 2 := by omega
              simp only [h1', h2', h3', h4', ↓reduceIte]
            · intro z hz
              rw [h'top] at hz
              rcases hR2 z hz with h | h | h
              · exact Or.inl h
              · exact Or.inr (by omega)
              · exact Or.inr (by omega)
          · -- a space split in place below an inner node: the second half linked from the parent
            have h2l := hlen (s + (e + 1)) (by omega) hD hNR hsp
            obtain ⟨r, hdiv, hsc, hscL, hlowL, hf, hs⟩ := chain_halves_factsR c.i (Nn (s + (e + 1))) ins
              hins h2l hxtimes hxwf
            have hXj := hXlt (s + (e + 1)) (by omega) (Nat.le_refl _)
            have hXq := hXlt (s + e) (by omega) (by omega)
            apply writerWP_handleFullWith_spaceInPlace_up (s + e) (X (s + (e + 1))) (X (s + e))
              (Nn (s + (e + 1))) (Nn (s + e)) ins c w hlk hlq (by simpa using hqlf) hmade hsp hpq hXj
            intro w1 h1n h1t h1top h1path h1next h1vals
            obtain ⟨out, hout⟩ : ∃ o, halves (Nn (s + (e + 1))).leaf c.i
                ((Nn (s + (e + 1))).lastVersion c.i) ins = o := ⟨_, rfl⟩
            rw [hout] at h1n hdiv hf hs ⊢
            rw [hdiv]
            have hN1 : wNode c.p base w1 = updN (updN (wNode c.p base w) (X (s + (e + 1))) out.1)
                w.next out.2.1 :=
              wNode_two_updN c.p base w w1 _ _ _ _ h1n h1t (by omega) htk htk0
            have hVS : ¬ TReach (updN (wNode c.p base w) (X (s + (e + 1)))
                (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + (e + 1)))))
                c.i w.top.rootKey w.next :=
              not_reach_fresh _ c.i _ _ hV (by rw [updN_ne _ _ _ _ (fun h => by omega)]; exact hwnext)
                (hVfresh w.next (Nat.le_refl _))
            obtain ⟨hTsub, hRsub⟩ := treeOK_updN_sub (wNode c.p base w) c.i w.top.rootKey
              (X (s + (e + 1))) _ out.1 hV (fun c' z h => (hf c' z h).2)
            have hS1' : ¬ TReach (updN (wNode c.p base w) (X (s + (e + 1))) out.1) c.i w.top.rootKey
                w.next := fun h => hVS (hRsub _ h)
            have hT1 : TreeOK (updN (updN (wNode c.p base w) (X (s + (e + 1))) out.1) w.next out.2.1)
                c.i w.top.rootKey := treeOK_updN_unreach _ c.i _ _ _ hTsub hS1'
            have hagree1 : ∀ z, TReach (updN (wNode c.p base w) (X (s + (e + 1))) out.1) c.i
                w.top.rootKey z → updN (updN (wNode c.p base w) (X (s + (e + 1))) out.1) w.next out.2.1 z =
                updN (wNode c.p base w) (X (s + (e + 1))) out.1 z :=
              fun z hz => updN_ne _ _ _ _ (fun he => hS1' (he ▸ hz))
            obtain ⟨hT2, hR2⟩ := treeOK_spaceInPlaceStep
              (updN (wNode c.p base w) (X (s + (e + 1)))
                (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + (e + 1)))))
              (updN (wNode c.p base w1) (X (s + e)) ([(r.1, w.next)].foldl
                (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + e))))
              c.i w.top.rootKey (X (s + e)) (X (s + (e + 1))) w.next
              (Nn (s + e)) (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + (e + 1))))
              out.1 out.2.1
              ([(r.1, w.next)].foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + e)))
              (K (s + (e + 1))) r.1 (splitLocalCv (Nn (s + (e + 1))).leaf r.1) hV hqR
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
            have hVR2 := rangeOrder_spaceInPlaceStep
              (updN (wNode c.p base w) (X (s + (e + 1)))
                (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + (e + 1)))))
              (updN (wNode c.p base w1) (X (s + e)) ([(r.1, w.next)].foldl
                (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + e))))
              c.i w.top.rootKey hVR hV (X (s + e)) (X (s + (e + 1))) w.next
              (Nn (s + e)) (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + (e + 1))))
              out.1 out.2.1
              ([(r.1, w.next)].foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + e)))
              (K (s + (e + 1))) r.1 hqR (by rw [updN_ne _ _ _ _ hqx]; exact hwq)
              (by simpa using hqlf) hkl (updN_self _ _ _)
              (by rw [updN_ne _ _ _ _ (fun h => by omega)]; exact hwnext)
              (hVfresh w.next (Nat.le_refl _)) hscL hlowL (updN_self _ _ _)
              (by simp only [List.foldl_cons, List.foldl_nil, KNode.add_leaf]; simpa using hqlf)
              (by
                intro c' z h
                simp only [List.foldl_cons, List.foldl_nil] at h
                exact KNode.add_key_liveAt_mem _ c.i _ _ hqwf hqtimes c' z h)
              (KNode.add_key_liveAt_self _ c.i _ _ hqwf hqtimes)
              (by
                rw [updN_ne _ _ _ _ (Ne.symm hqx), hN1, updN_ne _ _ _ _ (fun h => by omega)]
                exact updN_self _ _ _)
              (by
                have := (halves_leaf_flags (Nn (s + (e + 1))).leaf c.i
                  ((Nn (s + (e + 1))).lastVersion c.i) ins).1
                rw [hout] at this
                rw [this, KNode.addKeys_leaf])
              (fun c' z h => ⟨(hf c' z h).2, (hf c' z h).1⟩)
              (by
                rw [updN_ne _ _ _ _ (fun h => by omega), hN1]
                exact updN_self _ _ _)
              (by
                have := (halves_leaf_flags (Nn (s + (e + 1))).leaf c.i
                  ((Nn (s + (e + 1))).lastVersion c.i) ins).2
                rw [hout] at this
                rw [this, KNode.addKeys_leaf])
              (by
                intro c' z h
                obtain ⟨c0, h1, h2, h3⟩ := hs c' z h
                refine ⟨c0, h1, h3, ?_⟩
                rw [h2, splitLocalCv_eq, KNode.addKeys_leaf])
              (by
                intro z hz2 hz1 hz3
                rw [updN_ne _ _ _ _ hz2, hN1, updN_ne _ _ _ _ hz3, updN_ne _ _ _ _ hz1]
                exact (updN_ne _ _ _ _ hz1).symm)
            have hpar := ih (by omega) w1 [(r.1, w.next)] (Or.inl ⟨_, _, rfl⟩)
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
                have hne1 : ¬ X i = X (s + (e + 1)) := fun he => by
                  have := hdist _ _ h1 (by omega) (by omega) hD he; omega
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
                have h1' : ¬ z = X (s + (e + 1)) := by omega
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
                  by_cases hu1 : u = X (s + (e + 1))
                  · rw [hu1, updN_self] at hm
                    simp only [Option.some.injEq] at hm
                    subst hm
                    have := hvxLinks c' z (hf c' z hc).2; omega
                  · rw [updN_ne _ _ _ _ hu1] at hm
                    have := hS6 u c' z ⟨m, hm, hc⟩; omega)
              (fun h0 => by rw [h1top]; exact hR0 h0)
              (by rw [h1top]; exact hT2)
              (by rw [h1top]; exact hVR2)
            refine writerWP_mono hpar ?_
            rintro _ w2 ⟨hT2', ⟨h2top, h2t, h2path, h2next, h2vals⟩, h2frame, h2reach, h2R'⟩
            refine ⟨hT2', ⟨?_, by rw [h2t, h1t], by rw [h2path, h1path], by omega,
              by rw [h2vals, h1vals]⟩, ?_, ?_, h2R'⟩
            · rcases h2top with h | ⟨h0, h⟩
              · exact Or.inl (h.trans h1top)
              · exact Or.inr ⟨h0, by omega⟩
            · intro z hz hzX
              rw [h2frame z (by omega) (fun i h1 h2 => hzX i h1 (by omega)), h1n]
              have h1' : ¬ z = X (s + (e + 1)) := hzX _ (by omega) (Nat.le_refl _)
              have h2' : ¬ z = w.next := by omega
              simp only [h1', h2', ↓reduceIte]
            · intro z hz
              rcases h2reach z hz with h' | h'
              · rw [h1top] at h'
                rcases hR2 z h' with h'' | h''
                · exact Or.inl h''
                · exact Or.inr (by omega)
              · exact Or.inr (by omega)
        · by_cases hqlf : (Nn (s + e)).leaf = true
          · -- a space split below a leaf, the node not made: a new inner node above the halves
            have h2l := hlen (s + (e + 1)) (by omega) hD hNR hsp
            obtain ⟨r, hdiv, hsc, hscL, hlowL, hf, hs⟩ := chain_halves_factsR c.i (Nn (s + (e + 1))) ins
              hins h2l hxtimes hxwf
            apply writerWP_handleFullWith_segSpace_up (s + e) (X (s + (e + 1))) (X (s + e))
              (Nn (s + (e + 1))) (Nn (s + e)) (K (s + (e + 1))) ins c w hlk hlq hqlf hmade hsp hpq hpk
            intro w1 h1n h1t h1top h1path h1next h1vals
            obtain ⟨out, hout⟩ : ∃ o, halves (Nn (s + (e + 1))).leaf c.i
                ((Nn (s + (e + 1))).lastVersion c.i) ins = o := ⟨_, rfl⟩
            rw [hout] at h1n hdiv hf hs
            rw [hdiv] at h1n
            obtain ⟨hfree4, htk4, hbase4⟩ := hS5 (w.next + 2 + 2) (by omega)
            have hN1 : wNode c.p base w1 = updN (updN (updN (wNode c.p base w) w.next out.1)
                (w.next + 2) out.2.1) (w.next + 2 + 2)
                ⟨false, [.time c.i, .key 0 w.next, .key r.1 (w.next + 2)]⟩ :=
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
            have hnd : ([(0, w.next), (r.1, w.next + 2)].map Prod.fst).Nodup := by
              simp only [List.map_cons, List.map_nil, List.nodup_cons, List.mem_cons,
                List.not_mem_nil, or_false, List.nodup_nil, and_true, not_false_eq_true]
              omega
            have hrn : ∀ c' z, (c', z) ∈ (⟨false, [.time c.i, .key 0 w.next, .key r.1 (w.next + 2)]⟩ :
                KNode).liveAt c.i → (c' = 0 ∧ z = w.next) ∨ (c' = r.1 ∧ z = w.next + 2) := by
              intro c' z h
              have h' := (mrg_newKlongs_liveAt_iff false c.i [(0, w.next), (r.1, w.next + 2)] hnd c' z).mp h
              simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h'
              exact h'
            have hXj := hXlt (s + (e + 1)) (by omega) (Nat.le_refl _)
            have hXq := hXlt (s + e) (by omega) (by omega)
            obtain ⟨hT2, hR2⟩ := treeOK_segSpaceStep
              (updN (wNode c.p base w) (X (s + (e + 1)))
                (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + (e + 1)))))
              (updN (wNode c.p base w1) (X (s + e)) ([(K (s + (e + 1)), w.next + 2 + 2)].foldl
                (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + e))))
              c.i w.top.rootKey (X (s + e)) (X (s + (e + 1))) w.next (w.next + 2) (w.next + 2 + 2)
              (Nn (s + e)) (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + (e + 1))))
              out.1 out.2.1 ⟨false, [.time c.i, .key 0 w.next, .key r.1 (w.next + 2)]⟩
              ([(K (s + (e + 1)), w.next + 2 + 2)].foldl
                (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + e)))
              (K (s + (e + 1))) r.1 (splitLocalCv (Nn (s + (e + 1))).leaf r.1) hsc hV hqR
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
            have hVR2 := rangeOrder_segSpaceStep
              (updN (wNode c.p base w) (X (s + (e + 1)))
                (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + (e + 1)))))
              (updN (wNode c.p base w1) (X (s + e)) ([(K (s + (e + 1)), w.next + 2 + 2)].foldl
                (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + e))))
              c.i w.top.rootKey (X (s + e)) (X (s + (e + 1))) w.next (w.next + 2) (w.next + 2 + 2)
              (Nn (s + e)) ([(K (s + (e + 1)), w.next + 2 + 2)].foldl
                (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + e)))
              (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + (e + 1))))
              out.1 out.2.1 ⟨false, [.time c.i, .key 0 w.next, .key r.1 (w.next + 2)]⟩
              (K (s + (e + 1))) r.1 hVR hV hqR
              (by rw [updN_ne _ _ _ _ hqx]; exact hwq) hqlf hkl (updN_self _ _ _) (updN_self _ _ _)
              (by simp only [List.foldl_cons, List.foldl_nil, KNode.add_leaf]; exact hqlf)
              (by
                intro c' z h
                simp only [List.foldl_cons, List.foldl_nil] at h
                exact KNode.add_key_liveAt_mem _ c.i _ _ hqwf hqtimes c' z h)
              (Or.inr ⟨(by rw [updN_ne _ _ _ _ (fun h => by omega)]; exact hwnext),
                hVfresh w.next (Nat.le_refl _)⟩)
              (by rw [updN_ne _ _ _ _ (fun h => by omega)]; exact hwnext2)
              (hVfresh (w.next + 2) (by omega))
              (by
                rw [updN_ne _ _ _ _ (fun h => by omega)]
                simp only [wNode, htk4, Bool.false_eq_true, ↓reduceIte, hfree4, hbase4])
              (hVfresh (w.next + 2 + 2) (by omega))
              (by omega) (by omega) (by omega) hscL hsc
              (by
                rw [updN_ne _ _ _ _ (fun h => by omega), hN1]
                exact updN_self _ _ _)
              rfl hrn
              ((mrg_newKlongs_liveAt_iff false c.i [(0, w.next), (r.1, w.next + 2)] hnd r.1
                (w.next + 2)).mpr (by simp))
              (by
                rw [updN_ne _ _ _ _ (fun h => by omega), hN1,
                  updN_ne _ _ _ _ (fun h => by omega), updN_ne _ _ _ _ (fun h => by omega)]
                exact updN_self _ _ _)
              (by
                have := (halves_leaf_flags (Nn (s + (e + 1))).leaf c.i
                  ((Nn (s + (e + 1))).lastVersion c.i) ins).1
                rw [hout] at this
                rw [this, KNode.addKeys_leaf])
              (fun c' z h => ⟨(hf c' z h).2, (hf c' z h).1⟩)
              (by
                rw [updN_ne _ _ _ _ (fun h => by omega), hN1, updN_ne _ _ _ _ (fun h => by omega)]
                exact updN_self _ _ _)
              (by
                have := (halves_leaf_flags (Nn (s + (e + 1))).leaf c.i
                  ((Nn (s + (e + 1))).lastVersion c.i) ins).2
                rw [hout] at this
                rw [this, KNode.addKeys_leaf])
              (by
                intro c' z h
                obtain ⟨c0, h1, h2, h3⟩ := hs c' z h
                refine ⟨c0, h1, h3, ?_⟩
                rw [h2, splitLocalCv_eq, KNode.addKeys_leaf])
              (by
                intro z hz2 hz5 hz3 hz4 hz1
                rw [updN_ne _ _ _ _ hz2, hN1, updN_ne _ _ _ _ hz5, updN_ne _ _ _ _ hz4,
                  updN_ne _ _ _ _ hz3]
                exact (updN_ne _ _ _ _ hz1).symm)
            apply hfinish w1 [(K (s + (e + 1)), w.next + 2 + 2)] (wNode c.p base w1)
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
              hT2 hVR2 hR2
          · exact hstepS hmade (by simpa using hqlf) hsp
      rw [appendKlongs_step_dead]
      simp only [writerWP_bind, writerWP_read]
      rw [writerWP_getNode_known _ _ c w hlk]
      by_cases hsz : (Nn (s + (e + 1))).size + ins.length + 1 > c.p.M
      · simp only [hsz, ↓reduceIte]
        by_cases hsp : c.p.splitAbove < ((Nn (s + (e + 1))).lastVersion c.i).size
        · exact hSPACE hsp
        · apply hTIME false
          simp only [Bool.not_false, Bool.true_and, decide_eq_false_iff_not, gt_iff_lt]
          exact hsp
      · have hd : deadOver c.p (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y))
            (Nn (s + (e + 1)))) = true := by
          cases h : deadOver c.p (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y))
            (Nn (s + (e + 1)))) with
          | true => rfl
          | false => exact absurd ⟨by omega, h⟩ hroom
        simp only [hsz, hd, ↓reduceIte]
        exact hTIME true (by simp)
end SIS.Tree
