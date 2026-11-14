/-
A cascade of any kind keeps the writer's tree (bergdb 024-22, `OpTreeOK`):
time and space splits, in place for nodes the transaction made, below inner
nodes or segment leaves, up to the space root (`writerWP_appendKlongs_chainG`).
The walk is `writerWP_appendKlongs_chainGL`, which also keeps TP7's live counts
link by link (`LiveEdges`, bergdb 024-12; each step of the tree has its twin of
`LiveSteps.lean` beside it); `writerWP_appendKlongs_chainG` is its corollary.
-/
import SIS.Tree.WriterTreeChainTree
import SIS.Tree.LiveChain

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- The writer's lookup after three new nodes. -/
theorem wNode_three_updN (p : Params) (base : View BVal) (w w' : W) (y1 y2 y3 : NodeId)
    (m1 m2 m3 : KNode)
    (hn : ∀ z, w'.nodes.lookup z = if z = y1 then some m1 else if z = y2 then some m2
      else if z = y3 then some m3 else w.nodes.lookup z) (ht : w'.taken = w.taken)
    (h12 : y1 ≠ y2) (h13 : y1 ≠ y3) (h23 : y2 ≠ y3)
    (ht1 : w.taken.contains y1 = false) (ht2 : w.taken.contains y2 = false)
    (ht3 : w.taken.contains y3 = false) :
    wNode p base w' = updN (updN (updN (wNode p base w) y1 m1) y2 m2) y3 m3 := by
  funext z
  unfold wNode updN
  rw [ht, hn z]
  by_cases h3 : z = y3
  · subst h3
    have h1 : ¬ z = y1 := fun h => h13 h.symm
    have h2 : ¬ z = y2 := fun h => h23 h.symm
    simp only [ht3, h1, h2, Bool.false_eq_true, ↓reduceIte]
  · simp only [h3, ↓reduceIte]
    by_cases h2 : z = y2
    · subst h2
      have h1 : ¬ z = y1 := fun h => h12 h.symm
      simp only [ht2, h1, Bool.false_eq_true, ↓reduceIte]
    · simp only [h2, ↓reduceIte]
      by_cases h1 : z = y1
      · subst h1; simp only [ht1, Bool.false_eq_true, ↓reduceIte]
      · simp only [h1, ↓reduceIte]

/-- A key klong added at time t is live at t. -/
theorem KNode.add_key_liveAt_self (n : KNode) (t : Time) (cv : Nat) (v : NodeId)
    (hw : klongsWf n.ks = true) (ht : ∀ s, Klong.time s ∈ n.ks → s ≤ t) :
    (cv, v) ∈ (n.add t (.key cv v)).liveAt t := by
  have hat := KNode.add_times n t (.key cv v) (fun s h => by cases h) ht
  rw [KNode.liveAt_of_times _ t hat]
  apply mem_of_lookup_nodup
  rw [KNode.add_key_live_lookup_of_wf n t cv cv v hw]
  simp

/-- Nodes below the next id kept: the writer's lookup is kept there. -/
theorem wNode_low_agree (p : Params) (base : View BVal) (w w1 : W) (h1t : w1.taken = w.taken)
    (hlow : ∀ z, z < w.next → w1.nodes.lookup z = w.nodes.lookup z) :
    ∀ z, z < w.next → wNode p base w1 z = wNode p base w z := by
  intro z hz
  simp only [wNode, h1t, hlow z hz]

/-- A node's link repointed: the klong of the repointed compare value is the
new one, the others are the node's. -/
theorem KNode.repoint_link_facts (qn : KNode) (t : Time) (x R : NodeId) (k1 j : Nat)
    (hj : qn.linkIndex x k1 = some j) (hqt : ∀ s, Klong.time s ∈ qn.ks → s ≤ t) :
    (k1, R) ∈ (qn.repoint j R).liveAt t ∧ ∀ c z, (c, z) ∈ (qn.repoint j R).liveAt t →
      (c = k1 ∧ z = R) ∨ (c ≠ k1 ∧ (c, z) ∈ qn.liveAt t) := by
  have hrt := KNode.repoint_times qn j R t hqt
  refine ⟨?_, ?_⟩
  · rw [KNode.liveAt_of_times _ t hrt]
    apply mem_of_lookup_nodup
    rw [KNode.repoint_live_lookup qn x R k1 j hj k1]
    simp
  · intro c z hc
    rw [KNode.liveAt_of_times _ t hrt] at hc
    have hlk := lookup_of_mem_nodup _ (KNode.live_keys_nodup _) c z hc
    rw [KNode.repoint_live_lookup qn x R k1 j hj c] at hlk
    by_cases hck : k1 = c
    · subst hck; simp at hlk; exact Or.inl ⟨rfl, hlk.symm⟩
    · have hb : (k1 == c) = false := by simpa using hck
      rw [hb] at hlk
      simp only [Bool.false_eq_true, ↓reduceIte] at hlk
      refine Or.inr ⟨Ne.symm hck, ?_⟩
      rw [KNode.liveAt_of_times qn t hqt]
      exact mem_of_lookup_nodup _ c z hlk

/-- The access path's nodes above a node stay reached when the node changes. -/
theorem chain_anc_reach (N : NodeId → Option KNode) (t : Time) (r : NodeId) (X : Nat → NodeId)
    (s j : Nat) (hT : TreeOK N t r) (hR : TReach N t r (X s))
    (hlink : ∀ i, s < i → i ≤ j → ∃ k, TLink N t (X (i - 1)) k (X i)) (m : KNode) :
    ∀ i, s ≤ i → i < j → TReach (updN N (X j) m) t r (X i) := by
  obtain ⟨a, ha⟩ := hR.pathLen
  have hp : ∀ d, s + d ≤ j → PathLen N t r (X (s + d)) (a + d) := by
    intro d
    induction d with
    | zero => intro _; simpa using ha
    | succ d ih =>
      intro hd
      obtain ⟨k, hk⟩ := hlink (s + (d + 1)) (by omega) hd
      have h1 : s + (d + 1) - 1 = s + d := by omega
      rw [h1] at hk
      exact PathLen.link (ih (by omega)) hk
  intro i hi hij
  have hpi := hp (i - s) (by omega)
  have hi' : s + (i - s) = i := by omega
  rw [hi'] at hpi
  apply tReach_updN_of_short N t r (X j) m _ _ hpi
  intro b hb
  have hpj := hp (j - s) (by omega)
  have hj' : s + (j - s) = j := by omega
  rw [hj'] at hpj
  have := PathLen.depth_unique hT _ _ _ hpj hb
  omega

set_option maxHeartbeats 3200000 in
/-- `writerWP_appendKlongs_chainG` with `LiveEdges`: its walk and its post, and
`LiveEdges` after when the tree with the klongs put into X (s + e) meets it,
with the merges' thresholds. -/
theorem writerWP_appendKlongs_chainGL (c : Ctx) (base : View BVal)
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
      WriterWP (appendKlongs (s + e) (X (s + e)) ins) c w (fun _ w' =>
        TreeOK (wNode c.p base w') c.i w'.top.rootKey ∧
        ((w'.top = w.top ∨ (s = 0 ∧ w.next ≤ w'.top.rootKey)) ∧ w'.taken = w.taken ∧ w'.path = w.path ∧ w.next ≤ w'.next ∧ w'.vals = w.vals) ∧
        (∀ z, z < w.next → (∀ i, s ≤ i → i ≤ s + e → z ≠ X i) →
          w'.nodes.lookup z = w.nodes.lookup z) ∧
        (∀ z, TReach (wNode c.p base w') c.i w'.top.rootKey z →
          TReach (updN (wNode c.p base w) (X (s + e))
            (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + e)))) c.i
            w.top.rootKey z ∨ w.next ≤ z) ∧
            (MergeParamsOK c.p → LiveEdges c.p (updN (wNode c.p base w) (X (s + e))
              (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + e)))) c.i w.top.rootKey →
              LiveEdges c.p (wNode c.p base w') c.i w'.top.rootKey)) := by
  -- the room case at any level
  have hroomCase : ∀ e, s + e ≤ D → ∀ (w : W) (ins : List (Nat × NodeId)),
      w.nodes.lookup (X (s + e)) = some (Nn (s + e)) → w.taken.contains (X (s + e)) = false →
      (Nn (s + e)).size + ins.length + 1 ≤ c.p.M →
      deadOver c.p (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + e))) = false →
      TreeOK (updN (wNode c.p base w) (X (s + e))
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
            (MergeParamsOK c.p → LiveEdges c.p (updN (wNode c.p base w) (X (s + e))
              (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + e)))) c.i w.top.rootKey →
              LiveEdges c.p (wNode c.p base w') c.i w'.top.rootKey)) := by
    intro e _ w ins hlk htk hroom hdead hV
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
    · intro _ hL; rw [hN]; exact hL
  intro e
  induction e with
  | zero =>
    intro hD w ins hins hinsT hS1 hS2 hS3 hS4 hS5 hS6 hR0 hV
    obtain ⟨hlk, htk⟩ := hS2 s (Nat.le_refl _) (by omega)
    by_cases hroom : (Nn (s + 0)).size + ins.length + 1 ≤ c.p.M ∧
        deadOver c.p (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + 0))) = false
    · exact hroomCase 0 hD w ins hlk htk hroom.1 hroom.2 hV
    · have hs0 : s = 0 := by
        rcases htop with h | h
        · exfalso
          exact hroom ⟨by have := h.1; have := hins.length; simp only [Nat.add_zero]; omega,
            by simpa using h.2 ins hins.length⟩
        · exact h
      -- the space root splits: a time split or a space split, in place or not
      simp only [Nat.add_zero] at hroom hins hV ⊢
      subst hs0
      have hrk : w.top.rootKey = X 0 := hR0 rfl
      have hV0 : TreeOK (updN (wNode c.p base w) (X 0)
          (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn 0))) c.i (X 0) := by
        rw [hrk] at hV; exact hV
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
                (MergeParamsOK c.p → LiveEdges c.p (updN (wNode c.p base w) (X 0)
                  (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn 0))) c.i w.top.rootKey →
                  LiveEdges c.p (wNode c.p base w') c.i w'.top.rootKey)) := by
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
          refine ⟨by rw [hN', h'top]; exact hT', ⟨Or.inl h'top, h't, h'path, by omega, h'v⟩, ?_, ?_, ?_⟩
          · intro z _ hzX
            rw [h'n, lookup_upsert, ite_eq_right_of_eq_false _ _
              (eq_false (hzX 0 (Nat.le_refl _) (Nat.le_refl _)))]
          · intro z hz
            rw [hN', h'top] at hz
            exact Or.inl (hR' z hz)
          · intro _ hL
            rw [hN', h'top]
            exact liveEdges_updN_sub c.p (wNode c.p base w) c.i w.top.rootKey (X 0) _ _
              (hlsubOf l hl_times hl_look) (addKeys_leaf c.i ins (Nn 0)).symm
              (timeSplit_liveAt_length c.i ins (Nn 0) l (Nn 0).leaf hxwf hxtimes hl_times hl_look) hL
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
          have hLs := liveEdges_rootTimeStep c.p (updN (wNode c.p base w) (X 0)
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
          refine ⟨by rw [h'root]; exact hT', ⟨Or.inr ⟨rfl, by omega⟩, h't, h'path, by omega, h'v⟩,
            ?_, ?_, ?_⟩
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
          · intro _ hL
            rw [h'root]
            rw [hrk] at hL
            exact hLs (addKeys_leaf c.i ins (Nn 0)).symm
              (timeSplit_liveAt_length c.i ins (Nn 0) l (Nn 0).leaf hxwf hxtimes hl_times hl_look) hL
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
                (MergeParamsOK c.p → LiveEdges c.p (updN (wNode c.p base w) (X 0)
                  (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn 0))) c.i w.top.rootKey →
                  LiveEdges c.p (wNode c.p base w') c.i w'.top.rootKey)) := by
        intro up hsp
        have h2l := hlen 0 (Nat.le_refl _) (by omega) hNR hsp
        obtain ⟨r, hdiv, hsc, _, hf, hs⟩ := chain_halves_facts c.i (Nn 0) ins hins h2l hxtimes hxwf
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
          have hLs := liveEdges_rootSpaceInPlaceStep c.p (updN (wNode c.p base w) (X 0)
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
          refine ⟨by rw [h'root]; exact hT', ⟨Or.inr ⟨rfl, by omega⟩, h't, h'path, by omega, h'v⟩,
            ?_, ?_, ?_⟩
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
          · intro hp hL
            rw [h'root]
            rw [hrk] at hL
            obtain ⟨hH1, hH2⟩ := halves_halfOK c.p hp (Nn 0) c.i ins hsp
            obtain ⟨hl1, hl2⟩ := halves_leaf_flags (Nn 0).leaf c.i ((Nn 0).lastVersion c.i) ins
            rw [hout] at hH1 hH2 hl1 hl2
            exact hLs (hl1.trans (addKeys_leaf c.i ins (Nn 0)).symm)
              (hl2.trans (addKeys_leaf c.i ins (Nn 0)).symm) hH1 hH2
              (newRoot_liveAt_two c.i (X 0) w.next r.1 hsc) hL
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
          have hLs := liveEdges_rootSpaceStep c.p (updN (wNode c.p base w) (X 0)
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
          refine ⟨by rw [h'root]; exact hT', ⟨Or.inr ⟨rfl, by omega⟩, h't, h'path, by omega, h'v⟩,
            ?_, ?_, ?_⟩
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
          · intro hp hL
            rw [h'root]
            rw [hrk] at hL
            obtain ⟨hH1, hH2⟩ := halves_halfOK c.p hp (Nn 0) c.i ins hsp
            obtain ⟨hl1, hl2⟩ := halves_leaf_flags (Nn 0).leaf c.i ((Nn 0).lastVersion c.i) ins
            rw [hout] at hH1 hH2 hl1 hl2
            exact hLs (hl1.trans (addKeys_leaf c.i ins (Nn 0)).symm)
              (hl2.trans (addKeys_leaf c.i ins (Nn 0)).symm) hH1 hH2
              (newRoot_liveAt_two c.i w.next (w.next + 2) r.1 hsc) hL
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
    intro hD w ins hins hinsT hS1 hS2 hS3 hS4 hS5 hS6 hR0 hV
    have hj : s < s + (e + 1) := by omega
    obtain ⟨hlk, htk⟩ := hS2 (s + (e + 1)) (by omega) (Nat.le_refl _)
    obtain ⟨hlq, htq⟩ := hS2 (s + e) (by omega) (by omega)
    by_cases hroom : (Nn (s + (e + 1))).size + ins.length + 1 ≤ c.p.M ∧
        deadOver c.p (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + (e + 1)))) = false
    · exact hroomCase (e + 1) hD w ins hlk htk hroom.1 hroom.2 hV
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
          (∀ z, TReach (updN N1 (X (s + e)) (ins'.foldl (fun n (cv, y) => n.add c.i (.key cv y))
            (Nn (s + e)))) c.i w.top.rootKey z →
            (TReach (updN (wNode c.p base w) (X (s + (e + 1)))
              (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + (e + 1))))) c.i
              w.top.rootKey z ∨ New z) ∧ z ≠ X (s + (e + 1))) →
          (MergeParamsOK c.p → LiveEdges c.p (updN (wNode c.p base w) (X (s + (e + 1))) (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + (e + 1))))) c.i w.top.rootKey →
            LiveEdges c.p (updN N1 (X (s + e)) (ins'.foldl (fun n (cv, y) => n.add c.i (.key cv y))
              (Nn (s + e)))) c.i w.top.rootKey) →
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
                  (MergeParamsOK c.p → LiveEdges c.p (updN (wNode c.p base w) (X (s + (e + 1)))
                    (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + (e + 1))))) c.i w.top.rootKey →
                    LiveEdges c.p (wNode c.p base w3) c.i w3.top.rootKey))) := by
        intro w1 ins' N1 New hins' hinsT' h1path h1t h1top h1next h1vals hNew h1low hN1 hT1 hR1 hS5' hS6' hV1 hRV1 hLV1
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
        refine writerWP_mono hpar ?_
        rintro _ w2 ⟨hT2, ⟨h2top, h2t, h2path, h2next, h2vals⟩, h2frame, h2reach, h2live⟩
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
        · intro hp hL
          have h2 := h2live hp (by rw [hN1, h1top]; exact hLV1 hp hL)
          rw [hN3]
          exact liveEdges_of_agree c.p _ _ c.i _
            (fun z hz => updN_ne _ _ _ _ (fun he => hxR2 (he ▸ hz))) h2
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
                (MergeParamsOK c.p → LiveEdges c.p (updN (wNode c.p base w) (X (s + (e + 1)))
                  (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + (e + 1))))) c.i w.top.rootKey →
                  LiveEdges c.p (wNode c.p base w') c.i w'.top.rootKey)) := by
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
        have hL1V := liveEdges_timeSplit_gen c.p (updN (wNode c.p base w) (X (s + (e + 1)))
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
          (by rw [← hN1]; exact hR1V)
          (fun _ hL => by
            rw [← hN1]
            exact hL1V (addKeys_leaf c.i ins (Nn (s + (e + 1)))).symm
              (timeSplit_liveAt_length c.i ins (Nn (s + (e + 1))) l (Nn (s + (e + 1))).leaf hxwf hxtimes
                hl_times hl_look)
              (addKeys_leaf c.i _ _) (addKeys_liveAt_length c.i _ _ hqwf hqtimes) hL)
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
                (MergeParamsOK c.p → LiveEdges c.p (updN (wNode c.p base w) (X (s + (e + 1)))
                  (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + (e + 1))))) c.i w.top.rootKey →
                  LiveEdges c.p (wNode c.p base w') c.i w'.top.rootKey)) := by
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
        have hL1V := liveEdges_spaceSplit_gen c.p (updN (wNode c.p base w) (X (s + (e + 1)))
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
          (by rw [← hN1]; exact hR1V)
          (fun hp hL => by
            rw [← hN1]
            obtain ⟨hH1, hH2⟩ := halves_halfOK c.p hp (Nn (s + (e + 1))) c.i ins hsp
            obtain ⟨hl1, hl2⟩ := halves_leaf_flags (Nn (s + (e + 1))).leaf c.i
              ((Nn (s + (e + 1))).lastVersion c.i) ins
            rw [hout] at hH1 hH2 hl1 hl2
            exact hL1V (hl1.trans (addKeys_leaf c.i ins _).symm) (hl2.trans (addKeys_leaf c.i ins _).symm)
              hH1 hH2 (addKeys_leaf c.i _ _) (addKeys_liveAt_length c.i _ _ hqwf hqtimes) hL)
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
                (MergeParamsOK c.p → LiveEdges c.p (updN (wNode c.p base w) (X (s + (e + 1)))
                  (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + (e + 1))))) c.i w.top.rootKey →
                  LiveEdges c.p (wNode c.p base w') c.i w'.top.rootKey)) := by
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
          refine ⟨by rw [hN', h'top]; exact hT', ⟨Or.inl h'top, h't, h'path, by omega, h'v⟩, ?_, ?_, ?_⟩
          · intro z _ hzX
            rw [h'n, lookup_upsert, ite_eq_right_of_eq_false _ _ (eq_false (hzX _ (by omega) (Nat.le_refl _)))]
          · intro z hz
            rw [hN', h'top] at hz
            exact Or.inl (hR' z hz)
          · intro _ hL
            rw [hN', h'top]
            exact liveEdges_updN_sub c.p (wNode c.p base w) c.i w.top.rootKey (X (s + (e + 1))) _ _ hlsub
              (addKeys_leaf c.i ins (Nn (s + (e + 1)))).symm
              (timeSplit_liveAt_length c.i ins (Nn (s + (e + 1))) l (Nn (s + (e + 1))).leaf hxwf hxtimes
                hl_times hl_look) hL
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
                (MergeParamsOK c.p → LiveEdges c.p (updN (wNode c.p base w) (X (s + (e + 1)))
                  (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + (e + 1))))) c.i w.top.rootKey →
                  LiveEdges c.p (wNode c.p base w') c.i w'.top.rootKey)) := by
        intro hsp
        by_cases hmade : (Nn (s + (e + 1))).firstTime = some c.i
        · by_cases hqlf : (Nn (s + e)).leaf = true
          · -- a space split in place below a leaf: a new inner node above, the leaf repointed
            have h2l := hlen (s + (e + 1)) (by omega) hD hNR hsp
            obtain ⟨r, hdiv, hsc, _, hf, hs⟩ := chain_halves_facts c.i (Nn (s + (e + 1))) ins hins h2l
              hxtimes hxwf
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
            have hL2 := liveEdges_segSpaceInPlaceStep c.p
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
            refine ⟨by rw [h'top]; exact hT2, ⟨Or.inl h'top, h't, h'path, by omega, h'v⟩, ?_, ?_, ?_⟩
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
            · intro hp hL
              rw [h'top]
              obtain ⟨hH1, hH2⟩ := halves_halfOK c.p hp (Nn (s + (e + 1))) c.i ins hsp
              obtain ⟨hl1, hl2⟩ := halves_leaf_flags (Nn (s + (e + 1))).leaf c.i
                ((Nn (s + (e + 1))).lastVersion c.i) ins
              rw [hout] at hH1 hH2 hl1 hl2
              exact hL2 (hl1.trans (addKeys_leaf c.i ins _).symm) (hl2.trans (addKeys_leaf c.i ins _).symm)
                hH1 hH2 (newRoot_liveAt_two c.i (X (s + (e + 1))) w.next r.1 hsc)
                ((repoint_leaf_eq _ _ _).trans hqlf) (repoint_leaf_eq _ _ _)
                (repoint_liveAt_length (Nn (s + e)) (X (s + (e + 1))) (w.next + 2) (K (s + (e + 1))) j0
                  c.i hj0 hqtimes) hL
          · -- a space split in place below an inner node: the second half linked from the parent
            have h2l := hlen (s + (e + 1)) (by omega) hD hNR hsp
            obtain ⟨r, hdiv, hsc, _, hf, hs⟩ := chain_halves_facts c.i (Nn (s + (e + 1))) ins hins h2l
              hxtimes hxwf
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
            have hL2 := liveEdges_spaceInPlaceStep c.p
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
            refine writerWP_mono hpar ?_
            rintro _ w2 ⟨hT2', ⟨h2top, h2t, h2path, h2next, h2vals⟩, h2frame, h2reach, h2live⟩
            refine ⟨hT2', ⟨?_, by rw [h2t, h1t], by rw [h2path, h1path], by omega,
              by rw [h2vals, h1vals]⟩, ?_, ?_, ?_⟩
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
            · intro hp hL
              apply h2live hp
              rw [h1top]
              obtain ⟨hH1, hH2⟩ := halves_halfOK c.p hp (Nn (s + (e + 1))) c.i ins hsp
              obtain ⟨hl1, hl2⟩ := halves_leaf_flags (Nn (s + (e + 1))).leaf c.i
                ((Nn (s + (e + 1))).lastVersion c.i) ins
              rw [hout] at hH1 hH2 hl1 hl2
              exact hL2 (hl1.trans (addKeys_leaf c.i ins _).symm) (hl2.trans (addKeys_leaf c.i ins _).symm)
                hH1 hH2 (addKeys_leaf c.i _ _) (addKeys_liveAt_length c.i _ _ hqwf hqtimes) hL
        · by_cases hqlf : (Nn (s + e)).leaf = true
          · -- a space split below a leaf, the node not made: a new inner node above the halves
            have h2l := hlen (s + (e + 1)) (by omega) hD hNR hsp
            obtain ⟨r, hdiv, hsc, _, hf, hs⟩ := chain_halves_facts c.i (Nn (s + (e + 1))) ins hins h2l
              hxtimes hxwf
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
            have hL2 := liveEdges_segSpaceStep c.p
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
              hT2 hR2
              (fun hp hL => by
                obtain ⟨hH1, hH2⟩ := halves_halfOK c.p hp (Nn (s + (e + 1))) c.i ins hsp
                obtain ⟨hl1, hl2⟩ := halves_leaf_flags (Nn (s + (e + 1))).leaf c.i
                  ((Nn (s + (e + 1))).lastVersion c.i) ins
                rw [hout] at hH1 hH2 hl1 hl2
                exact hL2 (hl1.trans (addKeys_leaf c.i ins _).symm) (hl2.trans (addKeys_leaf c.i ins _).symm)
                  hH1 hH2 (newRoot_liveAt_two c.i w.next (w.next + 2) r.1 hsc)
                  ((addKeys_leaf c.i _ _).trans hqlf) (addKeys_leaf c.i _ _)
                  (addKeys_liveAt_length c.i _ _ hqwf hqtimes) hL)
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

/-- A cascade of splits of any kind and depth keeps the writer's tree (bergdb
024-22, `OpTreeOK`): the access path's nodes X s to X D, each below the one
before by klong K i. A full node splits in time or in space, in place if the
transaction made it (`firstTime = some c.i`), below an inner node or a segment
leaf; the cascade stops at X s, which has room for the klongs put or is the
space root (s = 0, which may split and get a new root above it). A full node
below an inner parent has its live compare values in the range of the parent's
link (`hrange`); a node that space splits has two live klongs (`hlen`). From a
state whose tree with the klongs put into X (s + e) is a tree, the writer's
tree after `appendKlongs (s + e)` is a tree; the top is kept unless the space
root split; nodes below the next id but the path's are kept; and every node
reached was reached in that tree or is new. Generalizes
`writerWP_appendKlongs_chain` (`chainC`), which takes inner parents and nodes
that existed before the transaction. -/
theorem writerWP_appendKlongs_chainG (c : Ctx) (base : View BVal)
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
      WriterWP (appendKlongs (s + e) (X (s + e)) ins) c w (fun _ w' =>
        TreeOK (wNode c.p base w') c.i w'.top.rootKey ∧
        ((w'.top = w.top ∨ (s = 0 ∧ w.next ≤ w'.top.rootKey)) ∧ w'.taken = w.taken ∧ w'.path = w.path ∧ w.next ≤ w'.next ∧ w'.vals = w.vals) ∧
        (∀ z, z < w.next → (∀ i, s ≤ i → i ≤ s + e → z ≠ X i) →
          w'.nodes.lookup z = w.nodes.lookup z) ∧
        (∀ z, TReach (wNode c.p base w') c.i w'.top.rootKey z →
          TReach (updN (wNode c.p base w) (X (s + e))
            (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + e)))) c.i
            w.top.rootKey z ∨ w.next ≤ z)) := by
  intro e hD w ins h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  exact writerWP_mono (writerWP_appendKlongs_chainGL c base path0 s D X K Nn hX hK hlinkK hrange hlen
    hwf htimes htop hdist e hD w ins h1 h2 h3 h4 h5 h6 h7 h8 h9 h10)
    (fun _ _ h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩)

end SIS.Tree
