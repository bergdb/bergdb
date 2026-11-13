import SIS.Tree.WriterTreeChainG
import SIS.Tree.GetCascadeIP
import SIS.Tree.GetCascadeChain

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! The reading after a cascade of splits of any kind (bergdb 024-12, TP10):
cost's `writerWP_appendKlongs_chainG` with the reading. The writer's state after
`appendKlongs j (X j) ins` reads as the state before with the klongs ins put in
X j, for every value lookup without values at the new ids and the chain's
nodes. Splits that make a new root (the space root's space split, a segment
root's space split below a segment leaf) are left out (`hspace`): the tree
grows a level there, and the reading's fuel must cover it. -/

/-- The halves of a node's last version with klongs put (InsOK) search as the
node with the klongs put: the first below the divider, the second from it. -/
theorem halves_read (t : Time) (n : KNode) (ins : List (Nat × NodeId)) (hins : InsOK n ins)
    (h2 : 2 ≤ n.live.length) (hnt : ∀ s, Klong.time s ∈ n.ks → s ≤ t) (hnwf : klongsWf n.ks = true) :
    (halves n.leaf t (n.lastVersion t) ins).1.leaf = (ins.foldl (fun n (cv, y) => n.add t (.key cv y)) n).leaf ∧
    (halves n.leaf t (n.lastVersion t) ins).2.1.leaf = (ins.foldl (fun n (cv, y) => n.add t (.key cv y)) n).leaf ∧
    ((ins.foldl (fun n (cv, y) => n.add t (.key cv y)) n).leaf = true → ∀ c : Nat,
      c < (halves n.leaf t (n.lastVersion t) ins).2.2 →
      ((halves n.leaf t (n.lastVersion t) ins).1.searchEq t c).map (·.y) =
        ((ins.foldl (fun n (cv, y) => n.add t (.key cv y)) n).searchEq t c).map (·.y)) ∧
    ((ins.foldl (fun n (cv, y) => n.add t (.key cv y)) n).leaf = true → ∀ c : Nat,
      (halves n.leaf t (n.lastVersion t) ins).2.2 ≤ c →
      ((halves n.leaf t (n.lastVersion t) ins).2.1.searchEq t c).map (·.y) =
        ((ins.foldl (fun n (cv, y) => n.add t (.key cv y)) n).searchEq t c).map (·.y)) ∧
    ((ins.foldl (fun n (cv, y) => n.add t (.key cv y)) n).leaf = false → ∀ c : Nat,
      c < (halves n.leaf t (n.lastVersion t) ins).2.2 →
      ((halves n.leaf t (n.lastVersion t) ins).1.searchLte t c).map (·.y) =
        ((ins.foldl (fun n (cv, y) => n.add t (.key cv y)) n).searchLte t c).map (·.y)) ∧
    ((ins.foldl (fun n (cv, y) => n.add t (.key cv y)) n).leaf = false → ∀ c : Nat,
      (halves n.leaf t (n.lastVersion t) ins).2.2 ≤ c →
      ((halves n.leaf t (n.lastVersion t) ins).2.1.searchLte t c).map (·.y) =
        ((ins.foldl (fun n (cv, y) => n.add t (.key cv y)) n).searchLte t c).map (·.y)) := by
  obtain ⟨r, hr⟩ := divider_exists n (by omega)
  have hrm := divider_mem_live n r hr
  have hsc := divider_pos' n r h2 hr
  obtain ⟨a, more, hins_eq, hside⟩ := hins.side r hrm
  obtain ⟨hdiv, _, _⟩ := halves_links n.leaf t n rfl a more r hr hsc hside
  rw [← hins_eq] at hdiv
  rw [hdiv]
  have hside' : (∀ q ∈ ins, r.1 ≤ q.1) ∨ (∀ q ∈ ins, q.1 < r.1) := by
    rw [hins_eq]
    by_cases ha : r.1 ≤ a.1
    · left; intro q hq; exact (hside q hq).mpr ha
    · right; intro q hq
      rcases Nat.lt_or_ge q.1 r.1 with h | h
      · exact h
      · exact absurd ((hside q hq).mp h) ha
  have hxv_wf := KNode.addKeys_wf t ins _ hnwf
  have hxv_t := KNode.addKeys_times t ins _ hnt
  have hQlook := KNode.addKeys_live_lookup t ins _ hnwf
  rw [KNode.addKeys_leaf]
  cases hxl : n.leaf with
  | true =>
    have hL := halves_leaf_searchEq_ins n (ins.foldl (fun n (cv, y) => n.add t (.key cv y)) n) t ins
      hxl r hr hside' hxv_wf hxv_t hQlook
    simp only at hL
    rw [hxl] at hL
    obtain ⟨_, h1, h2, _, _, _, _, h3, h4⟩ := hL
    refine ⟨h1, h2, fun _ => h3, fun _ => h4, ?_, ?_⟩
    · intro h; cases h
    · intro h; cases h
  | false =>
    have hL := halves_inner_searchLte_ins n (ins.foldl (fun n (cv, y) => n.add t (.key cv y)) n) t ins
      hxl r hr hsc hside' hxv_t hQlook
    simp only at hL
    rw [hxl] at hL
    obtain ⟨_, h1, h2, _, _, _, _, h3, h4⟩ := hL
    refine ⟨h1, h2, ?_, ?_, fun _ => h3, fun _ => h4⟩
    · intro h; cases h
    · intro h; cases h

set_option maxHeartbeats 4000000 in
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
theorem writerWP_appendKlongs_chainGRV (c : Ctx) (base : View BVal)
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
    (hdist : ∀ i i', s ≤ i → i ≤ D → s ≤ i' → i' ≤ D → X i = X i' → i = i')
    (hspace : ∀ i, s ≤ i → i ≤ D → ¬ ChainRoom c (Nn i) →
      c.p.splitAbove < ((Nn i).lastVersion c.i).size → s < i ∧ (Nn (i - 1)).leaf = false) :
    ∀ e, s + e ≤ D → ∀ (w : W) (ins : List (Nat × NodeId)),
      InsOK (Nn (s + e)) ins → (∀ q ∈ ins, q.2 < w.next) →
      w.path = path0 →
      (∀ i, s ≤ i → i ≤ s + e → w.nodes.lookup (X i) = some (Nn i) ∧ w.taken.contains (X i) = false) →
      TreeOK (wNode c.p base w) c.i w.top.rootKey →
      (∀ i, s ≤ i → i ≤ s + e → TReach (wNode c.p base w) c.i w.top.rootKey (X i)) →
      (∀ z, w.next ≤ z → w.nodes.lookup z = none ∧ w.taken.contains z = false ∧
        knodeOf c.p base z = none) →
      (∀ u c' z, TLink (wNode c.p base w) c.i u c' z → z < w.next) →
      (s = 0 → ¬ ChainRoom c (Nn 0) → w.top.rootKey = X 0) →
      (∀ z zn, wNode c.p base w z = some zn → klongsWf zn.ks = true) →
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
            w.top.rootKey z ∨ (w.next ≤ z ∧ z < w'.next)) ∧
        (∀ z zn, wNode c.p base w' z = some zn → klongsWf zn.ks = true) ∧
        (∀ Val : NodeId → Option Nat, (∀ z, (w.next ≤ z ∨ ∃ i, s ≤ i ∧ i ≤ s + e ∧ z = X i) → Val z = none) →
          ∀ key, getFromR (wNode c.p base w') Val c.i c.p.fuel key w'.top.rootKey =
          getFromR (updN (wNode c.p base w) (X (s + e))
            (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + e)))) Val c.i c.p.fuel key
            w.top.rootKey) ∧
          (∀ z, w'.next ≤ z → w'.nodes.lookup z = w.nodes.lookup z)) := by
  -- the room case at any level
  have hroomCase : ∀ e, s + e ≤ D → ∀ (w : W) (ins : List (Nat × NodeId)),
      w.nodes.lookup (X (s + e)) = some (Nn (s + e)) → w.taken.contains (X (s + e)) = false →
      (Nn (s + e)).size + ins.length + 1 ≤ c.p.M →
      deadOver c.p (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + e))) = false →
      (∀ z zn, wNode c.p base w z = some zn → klongsWf zn.ks = true) → X (s + e) < w.next →
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
            w.top.rootKey z ∨ (w.next ≤ z ∧ z < w'.next)) ∧
        (∀ z zn, wNode c.p base w' z = some zn → klongsWf zn.ks = true) ∧
        (∀ Val : NodeId → Option Nat, (∀ z, (w.next ≤ z ∨ ∃ i, s ≤ i ∧ i ≤ s + e ∧ z = X i) → Val z = none) →
          ∀ key, getFromR (wNode c.p base w') Val c.i c.p.fuel key w'.top.rootKey =
          getFromR (updN (wNode c.p base w) (X (s + e))
            (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + e)))) Val c.i c.p.fuel key
            w.top.rootKey) ∧
          (∀ z, w'.next ≤ z → w'.nodes.lookup z = w.nodes.lookup z)) := by
    intro e _ w ins hlk htk hroom hdead hW hXn hV
    refine writerWP_mono (writerWP_appendKlongs_addKeys (s + e) (X (s + e)) (Nn (s + e)) ins c w hlk
      hroom hdead) ?_
    intro _ w' hw'
    subst hw'
    have hN := wNode_upsert_updN c.p base w { w with nodes := upsert w.nodes (X (s + e)) (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + e))) } (X (s + e)) _ rfl rfl htk
    refine ⟨?_, ⟨Or.inl rfl, rfl, rfl, Nat.le_refl _, rfl⟩, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hN]; exact hV
    · intro z _ hz
      show (upsert w.nodes _ _).lookup z = _
      rw [lookup_upsert, ite_eq_right_of_eq_false _ _
        (eq_false (hz (s + e) (Nat.le_add_right _ _) (Nat.le_refl _)))]
    · intro z hz
      rw [hN] at hz
      exact Or.inl hz
    · intro z zn h
      rw [hN] at h
      by_cases hz : z = X (s + e)
      · rw [hz, updN_self] at h
        cases h
        exact KNode.addKeys_wf c.i ins _ (hwf (s + e) (by omega) (by omega))
      · rw [updN_ne _ _ _ _ hz] at h
        exact hW z zn h
    · intro Val _ key
      rw [hN]
    · intro z hz
      show (upsert w.nodes _ _).lookup z = _
      have hzX : z ≠ X (s + e) := by
        have : w.next ≤ z := hz
        omega
      rw [lookup_upsert]
      simp only [hzX, ↓reduceIte]
  intro e
  induction e with
  | zero =>
    intro hD w ins hins hinsT hS1 hS2 hS3 hS4 hS5 hS6 hR0 hW hV
    obtain ⟨hlk, htk⟩ := hS2 s (Nat.le_refl _) (by omega)
    by_cases hroom : (Nn (s + 0)).size + ins.length + 1 ≤ c.p.M ∧
        deadOver c.p (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + 0))) = false
    · exact hroomCase 0 hD w ins hlk htk hroom.1 hroom.2 hW (by
      rcases Nat.lt_or_ge (X s) w.next with h | h
      · exact h
      · have := (hS5 _ h).1; rw [hlk] at this; cases this) hV
    · have hs0 : s = 0 := by
        rcases htop with h | h
        · exfalso
          exact hroom ⟨by have := h.1; have := hins.length; simp only [Nat.add_zero]; omega,
            by simpa using h.2 ins hins.length⟩
        · exact h
      -- the space root splits: a time split or a space split, in place or not
      simp only [Nat.add_zero] at hroom hins hV ⊢
      subst hs0
      have hrk : w.top.rootKey = X 0 := hR0 rfl (fun ⟨h1, h2⟩ =>
        hroom ⟨by have := hins.length; omega, h2 ins hins.length⟩)
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
      -- a node with the live klongs of the node with the klongs put reads as it
      have hxv_wf0 := KNode.addKeys_wf c.i ins _ hxwf
      have hxv_t0 := KNode.addKeys_times c.i ins _ hxtimes
      have hxv_look0 : ∀ l : KNode,
          (∀ q', l.live.lookup q' = ins.foldl (pairLookupStep q') ((Nn 0).live.lookup q')) →
          ∀ c', (⟨(Nn 0).leaf, l.ks⟩ : KNode).live.lookup c' =
            (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn 0)).live.lookup c' := by
        intro l hl c'
        rw [KNode.addKeys_live_lookup c.i ins _ hxwf c']
        exact hl c'
      have hwfV0 : ∀ z zn, updN (wNode c.p base w) (X 0)
          (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn 0)) z = some zn →
          klongsWf zn.ks = true := by
        intro z zn h
        by_cases hz : z = X 0
        · rw [hz, updN_self] at h; cases h; exact hxv_wf0
        · rw [updN_ne _ _ _ _ hz] at h; exact hW z zn h
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
                w.top.rootKey z ∨ (w.next ≤ z ∧ z < w'.next)) ∧
            (∀ z zn, wNode c.p base w' z = some zn → klongsWf zn.ks = true) ∧
            (∀ Val : NodeId → Option Nat, (∀ z, (w.next ≤ z ∨ ∃ i, 0 ≤ i ∧ i ≤ 0 ∧ z = X i) → Val z = none) →
              ∀ key, getFromR (wNode c.p base w') Val c.i c.p.fuel key w'.top.rootKey =
              getFromR (updN (wNode c.p base w) (X 0)
                (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn 0))) Val c.i c.p.fuel key
                w.top.rootKey) ∧
              (∀ z, w'.next ≤ z → w'.nodes.lookup z = w.nodes.lookup z)) := by
        intro up compact hcs
        by_cases hmade : (Nn 0).firstTime = some c.i
        · -- the root time split in place
          refine writerWP_mono (writerWP_handleFullWith_timeInPlace_term0 up (X 0) (Nn 0) ins compact
            c w hlk hmade hcs) ?_
          rintro _ w' ⟨l, hl_leaf, hl_wf, hl_times, hl_look, h't, h'top, h'v, h'next, h'path, h'n⟩
          have hN' : wNode c.p base w' = updN (wNode c.p base w) (X 0) ⟨(Nn 0).leaf, l.ks⟩ :=
            wNode_upsert_updN c.p base w w' _ _ h'n h't htk
          obtain ⟨hT', hR'⟩ := treeOK_updN_sub (wNode c.p base w) c.i w.top.rootKey (X 0) _ _ hV
            (hlsubOf l hl_times hl_look)
          refine ⟨by rw [hN', h'top]; exact hT', ⟨Or.inl h'top, h't, h'path, by omega, h'v⟩, ?_, ?_,
            ?_, ?_, ?_⟩
          rotate_left 4
          · intro z hz
            rw [h'n, lookup_upsert]
            have : z ≠ X 0 := by omega
            simp only [this, ↓reduceIte]
          · intro z _ hzX
            rw [h'n, lookup_upsert, ite_eq_right_of_eq_false _ _
              (eq_false (hzX 0 (Nat.le_refl _) (Nat.le_refl _)))]
          · intro z hz
            rw [hN', h'top] at hz
            exact Or.inl (hR' z hz)
          · intro z zn h
            rw [hN'] at h
            by_cases hz : z = X 0
            · rw [hz, updN_self] at h; cases h; exact hl_wf
            · rw [updN_ne _ _ _ _ hz] at h; exact hW z zn h
          · intro Val _ key
            rw [hN', h'top]
            exact getFromR_congr_node (updN (wNode c.p base w) (X 0) ⟨(Nn 0).leaf, l.ks⟩)
              (updN (wNode c.p base w) (X 0) (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn 0)))
              Val c.i c.p.fuel (X 0) _ _
              (fun z hz => by rw [updN_ne _ _ _ _ hz, updN_ne _ _ _ _ hz]) (updN_self _ _ _)
              (updN_self _ _ _) (by simp only [KNode.addKeys_leaf]) hl_wf hxv_wf0 hl_times hxv_t0
              (hxv_look0 l hl_look) key _
        · -- the root time split: a new root
          refine writerWP_mono (writerWP_handleFullWith_rootTime_term up (X 0) (Nn 0) ins compact c w
            hlk hmade hcs hXlt0 hfree0) ?_
          rintro _ w' ⟨l, hl_leaf, hl_wf, hl_times, hl_look, h't, h'root, h'v, h'path, h'next, h'n⟩
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
          refine ⟨by rw [h'root]; exact hT', ⟨Or.inr ⟨rfl, by omega⟩, h't, h'path, by omega, h'v⟩,
            ?_, ?_, ?_, ?_, ?_⟩
          rotate_left 4
          · intro z hz
            rw [h'n]
            have h1' : ¬ z = X 0 := by omega
            have h2' : ¬ z = w.next := by omega
            simp only [h1', h2', ↓reduceIte]
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
          · intro z zn h
            rw [hN'] at h
            by_cases hz2 : z = w.next
            · rw [hz2, updN_self] at h; cases h; exact hl_wf
            · rw [updN_ne _ _ _ _ hz2] at h
              by_cases hz1 : z = X 0
              · rw [hz1, updN_self] at h; cases h; exact KNode.toPrev_wf _ _ hxwf
              · rw [updN_ne _ _ _ _ hz1] at h; exact hW z zn h
          · intro Val _ key
            rw [h'root, hrk]
            have hnf : ¬ TReach (updN (wNode c.p base w) (X 0)
                (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn 0))) c.i (X 0) w.next :=
              not_reach_fresh _ c.i _ _ hV0 (hVnone w.next (Nat.le_refl _))
                (hVfresh w.next (Nat.le_refl _))
            refine getFromR_rename_root _ (wNode c.p base w') Val c.i c.p.fuel (X 0) w.next _
              ⟨(Nn 0).leaf, l.ks⟩ (updN_self _ _ _) (by rw [hN']; exact updN_self _ _ _)
              (by simp only [KNode.addKeys_leaf]) ?_ ?_ (fun z zn _ h => hwfV0 z zn h) ?_ ?_ key
            · intro _ c'
              rw [KNode.searchEq_live (⟨(Nn 0).leaf, l.ks⟩ : KNode) c.i hl_wf hl_times,
                KNode.searchEq_live (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn 0)) c.i
                  hxv_wf0 hxv_t0, hxv_look0 l hl_look]
            · intro _ c'
              exact KNode.searchLte_congr (⟨(Nn 0).leaf, l.ks⟩ : KNode)
                (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn 0)) c.i hl_times hxv_t0
                (hxv_look0 l hl_look) c'
            · intro z hz hzX
              have hzn : z ≠ w.next := fun h => hnf (h ▸ reachS_tReach _ _ _ _ hz)
              rw [hN', updN_ne _ _ _ _ hzn, updN_ne _ _ _ _ hzX, updN_ne _ _ _ _ hzX]
            · intro z zn c' hz hzn hc
              exact hV0.rootFree z c' (reachS_tReach _ _ _ _ hz) ⟨zn, hzn, hc⟩
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
                w.top.rootKey z ∨ (w.next ≤ z ∧ z < w'.next)) ∧
            (∀ z zn, wNode c.p base w' z = some zn → klongsWf zn.ks = true) ∧
            (∀ Val : NodeId → Option Nat, (∀ z, (w.next ≤ z ∨ ∃ i, 0 ≤ i ∧ i ≤ 0 ∧ z = X i) → Val z = none) →
              ∀ key, getFromR (wNode c.p base w') Val c.i c.p.fuel key w'.top.rootKey =
              getFromR (updN (wNode c.p base w) (X 0)
                (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn 0))) Val c.i c.p.fuel key
                w.top.rootKey) ∧
              (∀ z, w'.next ≤ z → w'.nodes.lookup z = w.nodes.lookup z)) := by
        intro up hsp
        exact absurd (hspace 0 (Nat.le_refl _) (by omega) hNR hsp).1 (Nat.lt_irrefl 0)
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
    intro hD w ins hins hinsT hS1 hS2 hS3 hS4 hS5 hS6 hR0 hW hV
    have hj : s < s + (e + 1) := by omega
    obtain ⟨hlk, htk⟩ := hS2 (s + (e + 1)) (by omega) (Nat.le_refl _)
    obtain ⟨hlq, htq⟩ := hS2 (s + e) (by omega) (by omega)
    by_cases hroom : (Nn (s + (e + 1))).size + ins.length + 1 ≤ c.p.M ∧
        deadOver c.p (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + (e + 1)))) = false
    · exact hroomCase (e + 1) hD w ins hlk htk hroom.1 hroom.2 hW (by
      rcases Nat.lt_or_ge (X (s + (e + 1))) w.next with h | h
      · exact h
      · have := (hS5 _ h).1; rw [hlk] at this; cases this) hV
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
      -- the facts of the reading at this level
      have hxv_wf := KNode.addKeys_wf c.i ins _ hxwf
      have hxv_t := KNode.addKeys_times c.i ins _ hxtimes
      have hwfV : ∀ z zn, ReachS (updN (wNode c.p base w) (X (s + (e + 1))) (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + (e + 1))))) c.i w.top.rootKey z → (updN (wNode c.p base w) (X (s + (e + 1))) (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + (e + 1))))) z = some zn →
          klongsWf zn.ks = true := by
        intro z zn _ h
        by_cases hz : z = X (s + (e + 1))
        · rw [hz, updN_self] at h; cases h; exact hxv_wf
        · rw [updN_ne _ _ _ _ hz] at h; exact hW z zn h
      have hrootN : ∀ z, w.next ≤ z → w.top.rootKey ≠ z := by
        intro z hz h
        obtain ⟨m, hm⟩ := hS3.rootKey
        have hwz : wNode c.p base w z = none := by
          obtain ⟨a, b, d⟩ := hS5 z hz
          simp only [wNode, b, Bool.false_eq_true, ↓reduceIte, a, d]
        rw [h, hwz] at hm; cases hm
      have hrootX : w.top.rootKey ≠ X (s + (e + 1)) := by
        intro h
        exact hV.rootFree (X (s + e)) (K (s + (e + 1))) hqR
          ⟨Nn (s + e), by rw [updN_ne _ _ _ _ hqx]; exact hwq, by rw [h]; exact hkl⟩
      have hVq : (updN (wNode c.p base w) (X (s + (e + 1))) (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + (e + 1))))) (X (s + e)) = some (Nn (s + e)) := by rw [updN_ne _ _ _ _ hqx]; exact hwq
      have hrqV : ReachS (updN (wNode c.p base w) (X (s + (e + 1))) (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + (e + 1))))) c.i w.top.rootKey (X (s + e)) := tReach_reachS _ _ _ _ hqR
      have hXn : ∀ z, w.next ≤ z → z ≠ X (s + (e + 1)) := by
        intro z hz h; have := hXlt (s + (e + 1)) (by omega) (Nat.le_refl _); omega
      have hQn : ∀ z, w.next ≤ z → z ≠ X (s + e) := by
        intro z hz h; have := hXlt (s + e) (by omega) (by omega); omega
      have hVfr : ∀ z, w.next ≤ z → (updN (wNode c.p base w) (X (s + (e + 1))) (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + (e + 1))))) z = none := by
        intro z hz
        rw [updN_ne _ _ _ _ (hXn z hz)]
        obtain ⟨a, b, d⟩ := hS5 z hz
        simp only [wNode, b, Bool.false_eq_true, ↓reduceIte, a, d]
      have hvalx : ∀ Val : NodeId → Option Nat,
          (∀ z, (w.next ≤ z ∨ ∃ i, s ≤ i ∧ i ≤ s + (e + 1) ∧ z = X i) → Val z = none) →
          ∀ z, w.next ≤ z → Val (X (s + (e + 1))) = Val z := by
        intro Val hVal z hz
        rw [hVal _ (Or.inr ⟨s + (e + 1), by omega, Nat.le_refl _, rfl⟩), hVal _ (Or.inl hz)]
      -- the rest of a split: the parent's step by the induction, then the node left behind
      have hfinish : ∀ (w1 : W) (ins' : List (Nat × NodeId)) (N1 : NodeId → Option KNode)
          (New : NodeId → Prop),
          InsOK (Nn (s + e)) ins' → (∀ q ∈ ins', q.2 < w1.next) →
          w1.path = w.path → w1.taken = w.taken → w1.top = w.top → w.next + 2 ≤ w1.next →
          w1.vals = w.vals → (∀ z, New z → w.next ≤ z ∧ z < w1.next) →
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
          (∀ z zn, N1 z = some zn → klongsWf zn.ks = true) →
          (∀ Val : NodeId → Option Nat,
            (∀ z, (w.next ≤ z ∨ ∃ i, s ≤ i ∧ i ≤ s + (e + 1) ∧ z = X i) → Val z = none) →
            ∀ key, getFromR (updN N1 (X (s + e)) (ins'.foldl (fun n (cv, y) => n.add c.i (.key cv y))
            (Nn (s + e)))) Val c.i c.p.fuel key w.top.rootKey =
            getFromR (updN (wNode c.p base w) (X (s + (e + 1)))
              (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + (e + 1)))))
              Val c.i c.p.fuel key w.top.rootKey) →
          (∀ z, w1.next ≤ z → w1.nodes.lookup z = w.nodes.lookup z) →
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
                  w.top.rootKey z ∨ (w.next ≤ z ∧ z < w3.next)) ∧
              (∀ z zn, wNode c.p base w3 z = some zn → klongsWf zn.ks = true) ∧
              (∀ Val : NodeId → Option Nat, (∀ z, (w.next ≤ z ∨ ∃ i, s ≤ i ∧ i ≤ s + (e + 1) ∧ z = X i) → Val z = none) →
                ∀ key, getFromR (wNode c.p base w3) Val c.i c.p.fuel key w3.top.rootKey =
                getFromR (updN (wNode c.p base w) (X (s + (e + 1)))
                  (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + (e + 1))))) Val c.i c.p.fuel key
                  w.top.rootKey) ∧
                (∀ z, w3.next ≤ z → w3.nodes.lookup z = w.nodes.lookup z))) := by
        intro w1 ins' N1 New hins' hinsT' h1path h1t h1top h1next h1vals hNew h1low hN1 hT1 hR1 hS5' hS6' hV1 hRV1 hW1 hlev hab1
        have hpar := ih (by omega) w1 ins' hins' hinsT' (by rw [h1path, hS1])
          (by
            intro i h1 h2
            obtain ⟨a, b⟩ := hS2 i h1 (by omega)
            refine ⟨?_, by rw [h1t]; exact b⟩
            rw [h1low _ (hXlt i h1 (by omega)), a])
          (by rw [hN1, h1top]; exact hT1)
          (by intro i h1 h2; rw [hN1, h1top]; exact hR1 i h1 h2)
          hS5' (by rw [hN1]; exact hS6') (fun h0 hnr => by rw [h1top]; exact hR0 h0 hnr)
          (by rw [hN1]; exact hW1)
          (by rw [hN1, h1top]; exact hV1)
        refine writerWP_mono hpar ?_
        rintro _ w2 ⟨hT2, ⟨h2top, h2t, h2path, h2next, h2vals⟩, h2frame, h2reach, h2W, h2R, h2ab⟩
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
        refine ⟨?_, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
        rotate_left 10
        · intro z hz
          have h3x : w3.next = w2.next := by rw [← hw3]
          try rw [h3x] at hz
          have hzX : z ≠ X (s + (e + 1)) := by
            have := hXlt (s + (e + 1)) (by omega) (Nat.le_refl _); omega
          try rw [h3n]
          rw [lookup_upsert]
          simp only [hzX, ↓reduceIte]
          rw [h2ab z hz, hab1 z (by omega)]
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
            · have h3x' : w3.next = w2.next := by rw [← hw3]
              have := hNew z h''
              exact Or.inr ⟨this.1, by omega⟩
          · have h3x' : w3.next = w2.next := by rw [← hw3]
            exact Or.inr (by omega)
        · intro z zn h
          rw [hN3] at h
          by_cases hz : z = X (s + (e + 1))
          · rw [hz, updN_self] at h
            cases h
            exact KNode.toPrev_wf _ _ (hwf (s + (e + 1)) (by omega) hD)
          · rw [updN_ne _ _ _ _ hz] at h
            exact h2W z zn h
        · intro Val hVal key
          have h3top : w3.top = w2.top := by rw [← hw3]
          rw [hN3]
          try rw [h3top]
          rw [getFromR_updN_unreach' (wNode c.p base w2) Val c.i c.p.fuel w2.top.rootKey
            (X (s + (e + 1))) _ (fun z zn _ h => h2W z zn h)
            (fun h => hxR2 (reachS_tReach _ _ _ _ h)) key]
          rw [h2R Val (fun z hz => hVal z (by
            rcases hz with h | ⟨i, h1, h2, h3⟩
            · exact Or.inl (by omega)
            · exact Or.inr ⟨i, h1, by omega, h3⟩)) key, h1top, hN1]
          exact hlev Val hVal key
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
                w.top.rootKey z ∨ (w.next ≤ z ∧ z < w'.next)) ∧
            (∀ z zn, wNode c.p base w' z = some zn → klongsWf zn.ks = true) ∧
            (∀ Val : NodeId → Option Nat, (∀ z, (w.next ≤ z ∨ ∃ i, s ≤ i ∧ i ≤ s + (e + 1) ∧ z = X i) → Val z = none) →
              ∀ key, getFromR (wNode c.p base w') Val c.i c.p.fuel key w'.top.rootKey =
              getFromR (updN (wNode c.p base w) (X (s + (e + 1)))
                (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + (e + 1))))) Val c.i c.p.fuel key
                w.top.rootKey) ∧
              (∀ z, w'.next ≤ z → w'.nodes.lookup z = w.nodes.lookup z)) := by
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
          (by
            intro z zn h
            by_cases hz : z = w.next
            · rw [hz, updN_self] at h; cases h; exact hl_wf
            · rw [updN_ne _ _ _ _ hz] at h; exact hW z zn h)
          (by
            intro Val hVal
            cases hqlf : (Nn (s + e)).leaf with
            | false =>
              exact getFromR_timeLevel _ _ Val c.i c.p.fuel w.top.rootKey (X (s + e))
                (X (s + (e + 1))) w.next (Nn (s + e)) _ ⟨(Nn (s + (e + 1))).leaf, l.ks⟩
                (K (s + (e + 1))) hV hwfV hVq hrqV hqlf hqwf hqtimes hkl hqx (updN_self _ _ _) hxv_wf
                hxv_t (hVfr w.next (Nat.le_refl _))
                (fun u c' hu => hVfresh w.next (Nat.le_refl _) u c' (reachS_tReach _ _ _ _ hu))
                (by rw [updN_ne _ _ _ _ (hQn w.next (Nat.le_refl _)), updN_self])
                (by simp only [KNode.addKeys_leaf]) hl_wf hl_times
                (fun c' => by rw [KNode.addKeys_live_lookup c.i ins _ hxwf c']; exact hl_look c')
                (updN_self _ _ _)
                (by intro z h1 h2 h3; rw [updN_ne _ _ _ _ h2, updN_ne _ _ _ _ h3, updN_ne _ _ _ _ h1])
                (hvalx Val hVal w.next (Nat.le_refl _)) (hrootN w.next (Nat.le_refl _)) hrootX
            | true =>
              exact getFromR_segTimeLevel _ _ Val c.i c.p.fuel w.top.rootKey (X (s + e))
                (X (s + (e + 1))) w.next (Nn (s + e)) _ ⟨(Nn (s + (e + 1))).leaf, l.ks⟩
                (K (s + (e + 1))) hV hwfV hVq hrqV hqlf hqwf hqtimes hkl hqx (updN_self _ _ _) hxv_wf
                hxv_t (hVfr w.next (Nat.le_refl _))
                (fun u c' hu => hVfresh w.next (Nat.le_refl _) u c' (reachS_tReach _ _ _ _ hu))
                (by rw [updN_ne _ _ _ _ (hQn w.next (Nat.le_refl _)), updN_self])
                (by simp only [KNode.addKeys_leaf]) hl_wf hl_times
                (fun c' => by rw [KNode.addKeys_live_lookup c.i ins _ hxwf c']; exact hl_look c')
                (updN_self _ _ _)
                (by intro z h1 h2 h3; rw [updN_ne _ _ _ _ h2, updN_ne _ _ _ _ h3, updN_ne _ _ _ _ h1])
                (hvalx Val hVal w.next (Nat.le_refl _)) (hrootN w.next (Nat.le_refl _)) hrootX)
          (by
            intro z hz
            rw [h1next] at hz
            rw [h1n]
            exact lookup_append_single_ne _ _ _ _ (by omega))
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
                w.top.rootKey z ∨ (w.next ≤ z ∧ z < w'.next)) ∧
            (∀ z zn, wNode c.p base w' z = some zn → klongsWf zn.ks = true) ∧
            (∀ Val : NodeId → Option Nat, (∀ z, (w.next ≤ z ∨ ∃ i, s ≤ i ∧ i ≤ s + (e + 1) ∧ z = X i) → Val z = none) →
              ∀ key, getFromR (wNode c.p base w') Val c.i c.p.fuel key w'.top.rootKey =
              getFromR (updN (wNode c.p base w) (X (s + (e + 1)))
                (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + (e + 1))))) Val c.i c.p.fuel key
                w.top.rootKey) ∧
              (∀ z, w'.next ≤ z → w'.nodes.lookup z = w.nodes.lookup z)) := by
        intro hfirst hql hsp
        have h2l := hlen (s + (e + 1)) (by omega) hD hNR hsp
        obtain ⟨r, hr⟩ := divider_exists (Nn (s + (e + 1))) (by omega)
        have hrm := divider_mem_live _ r hr
        have hsc := divider_pos' _ r h2l hr
        obtain ⟨a, more, hins_eq, hside⟩ := hins.side r hrm
        obtain ⟨hdiv, hfh, hsh⟩ := halves_links (Nn (s + (e + 1))).leaf c.i (Nn (s + (e + 1))) rfl
          a more r hr hsc hside
        rw [← hins_eq] at hdiv hfh hsh
        have hhalf := halves_read c.i (Nn (s + (e + 1))) ins hins h2l hxtimes hxwf
        have hwh := halves_newKlongs_wf (Nn (s + (e + 1))).leaf c.i (Nn (s + (e + 1))).live ins
        rw [← KNode.lastVersion_eq_newKlongs] at hwh
        apply writerWP_handleFullWith_space_up (s + e) (X (s + (e + 1))) (X (s + e)) (Nn (s + (e + 1)))
          (Nn (s + e)) (K (s + (e + 1))) ins c w hlk hlq hql hfirst hsp hpq hpk
        intro w1 h1n h1t h1top h1path h1next h1vals
        obtain ⟨out, hout⟩ : ∃ o, halves (Nn (s + (e + 1))).leaf c.i ((Nn (s + (e + 1))).lastVersion c.i) ins = o :=
          ⟨_, rfl⟩
        rw [hout] at h1n hdiv hfh hsh hhalf hwh ⊢
        rw [hdiv] at hhalf
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
          (by
            intro z zn h
            by_cases hz2 : z = w.next + 2
            · rw [hz2, updN_self] at h; cases h; exact hwh.2
            · rw [updN_ne _ _ _ _ hz2] at h
              by_cases hz1 : z = w.next
              · rw [hz1, updN_self] at h; cases h; exact hwh.1
              · rw [updN_ne _ _ _ _ hz1] at h; exact hW z zn h)
          (by
            intro Val hVal
            exact getFromR_spaceLevel _ _ Val c.i c.p.fuel w.top.rootKey (X (s + e)) (X (s + (e + 1)))
              w.next (w.next + 2) (Nn (s + e)) _ out.1 out.2.1 (K (s + (e + 1))) r.1 hV hwfV hVq hrqV
              hql hqwf hqtimes hkl hqx hrK.1
              (fun c' z hcz => by
                by_cases hle : c' ≤ K (s + (e + 1))
                · exact Or.inl hle
                · exact Or.inr (hrK.2 c' z hcz (by omega)))
              (updN_self _ _ _) (hVfr w.next (Nat.le_refl _)) (hVfr (w.next + 2) (by omega))
              (fun u c' z hu hl => ⟨fun h => by
                  subst h; exact hVfresh _ (Nat.le_refl _) u c' (reachS_tReach _ _ _ _ hu) hl,
                fun h => by
                  subst h; exact hVfresh _ (by omega) u c' (reachS_tReach _ _ _ _ hu) hl⟩)
              (by rw [updN_ne _ _ _ _ (hQn w.next (Nat.le_refl _)), updN_ne _ _ _ _ h12, updN_self])
              (by rw [updN_ne _ _ _ _ (hQn (w.next + 2) (by omega)), updN_self])
              hhalf.1 hhalf.2.1 hhalf.2.2.1 hhalf.2.2.2.1 hhalf.2.2.2.2.1 hhalf.2.2.2.2.2
              (updN_self _ _ _)
              (by
                intro z h1 h2 h3 h4
                rw [updN_ne _ _ _ _ h2, updN_ne _ _ _ _ h4, updN_ne _ _ _ _ h3, updN_ne _ _ _ _ h1])
              hrootX (hrootN w.next (Nat.le_refl _)) (hrootN (w.next + 2) (by omega)))
          (by
            intro z hz
            rw [h1next] at hz
            rw [h1n]
            have h1' : ¬ z = w.next := by omega
            have h2' : ¬ z = w.next + 2 := by omega
            simp only [h1', h2', ↓reduceIte])
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
                w.top.rootKey z ∨ (w.next ≤ z ∧ z < w'.next)) ∧
            (∀ z zn, wNode c.p base w' z = some zn → klongsWf zn.ks = true) ∧
            (∀ Val : NodeId → Option Nat, (∀ z, (w.next ≤ z ∨ ∃ i, s ≤ i ∧ i ≤ s + (e + 1) ∧ z = X i) → Val z = none) →
              ∀ key, getFromR (wNode c.p base w') Val c.i c.p.fuel key w'.top.rootKey =
              getFromR (updN (wNode c.p base w) (X (s + (e + 1)))
                (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + (e + 1))))) Val c.i c.p.fuel key
                w.top.rootKey) ∧
              (∀ z, w'.next ≤ z → w'.nodes.lookup z = w.nodes.lookup z)) := by
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
          refine ⟨by rw [hN', h'top]; exact hT', ⟨Or.inl h'top, h't, h'path, by omega, h'v⟩, ?_, ?_,
            ?_, ?_, ?_⟩
          rotate_left 4
          · intro z hz
            have hzX : z ≠ X (s + (e + 1)) := by
              have := hXlt (s + (e + 1)) (by omega) (Nat.le_refl _); omega
            rw [h'n, lookup_upsert]
            simp only [hzX, ↓reduceIte]
          · intro z _ hzX
            rw [h'n, lookup_upsert, ite_eq_right_of_eq_false _ _ (eq_false (hzX _ (by omega) (Nat.le_refl _)))]
          · intro z hz
            rw [hN', h'top] at hz
            exact Or.inl (hR' z hz)
          · intro z zn h
            rw [hN'] at h
            by_cases hz : z = X (s + (e + 1))
            · rw [hz, updN_self] at h; cases h; exact hl_wf
            · rw [updN_ne _ _ _ _ hz] at h; exact hW z zn h
          · intro Val _ key
            rw [hN', h'top]
            exact getFromR_congr_node
              (updN (wNode c.p base w) (X (s + (e + 1))) ⟨(Nn (s + (e + 1))).leaf, l.ks⟩)
              (updN (wNode c.p base w) (X (s + (e + 1)))
                (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + (e + 1)))))
              Val c.i c.p.fuel (X (s + (e + 1))) _ _
              (fun z hz => by rw [updN_ne _ _ _ _ hz, updN_ne _ _ _ _ hz]) (updN_self _ _ _)
              (updN_self _ _ _) (by simp only [KNode.addKeys_leaf]) hl_wf hxv_wf hl_times hxv_t
              (fun c' => by rw [KNode.addKeys_live_lookup c.i ins _ hxwf c']; exact hl_look c') key _
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
                w.top.rootKey z ∨ (w.next ≤ z ∧ z < w'.next)) ∧
            (∀ z zn, wNode c.p base w' z = some zn → klongsWf zn.ks = true) ∧
            (∀ Val : NodeId → Option Nat, (∀ z, (w.next ≤ z ∨ ∃ i, s ≤ i ∧ i ≤ s + (e + 1) ∧ z = X i) → Val z = none) →
              ∀ key, getFromR (wNode c.p base w') Val c.i c.p.fuel key w'.top.rootKey =
              getFromR (updN (wNode c.p base w) (X (s + (e + 1)))
                (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + (e + 1))))) Val c.i c.p.fuel key
                w.top.rootKey) ∧
              (∀ z, w'.next ≤ z → w'.nodes.lookup z = w.nodes.lookup z)) := by
        intro hsp
        by_cases hmade : (Nn (s + (e + 1))).firstTime = some c.i
        · by_cases hqlf : (Nn (s + e)).leaf = true
          · -- a space split in place below a leaf: left out (hspace)
            exfalso
            have h := (hspace (s + (e + 1)) (by omega) hD hNR hsp).2
            have he : s + (e + 1) - 1 = s + e := by omega
            rw [he, hqlf] at h
            cases h
          · -- a space split in place below an inner node: the second half linked from the parent
            have h2l := hlen (s + (e + 1)) (by omega) hD hNR hsp
            obtain ⟨r, hdiv, hsc, hrm, hf, hs⟩ := chain_halves_facts c.i (Nn (s + (e + 1))) ins hins h2l
              hxtimes hxwf
            have hhalf := halves_read c.i (Nn (s + (e + 1))) ins hins h2l hxtimes hxwf
            have hwh := halves_newKlongs_wf (Nn (s + (e + 1))).leaf c.i (Nn (s + (e + 1))).live ins
            rw [← KNode.lastVersion_eq_newKlongs] at hwh
            have hql' : (Nn (s + e)).leaf = false := by simpa using hqlf
            have hrK := hrange (s + (e + 1)) hj hD hNR (by simpa using hql') r.1 r.2 hrm hsc
            have hXj := hXlt (s + (e + 1)) (by omega) (Nat.le_refl _)
            have hXq := hXlt (s + e) (by omega) (by omega)
            apply writerWP_handleFullWith_spaceInPlace_up (s + e) (X (s + (e + 1))) (X (s + e))
              (Nn (s + (e + 1))) (Nn (s + e)) ins c w hlk hlq (by simpa using hqlf) hmade hsp hpq hXj
            intro w1 h1n h1t h1top h1path h1next h1vals
            obtain ⟨out, hout⟩ : ∃ o, halves (Nn (s + (e + 1))).leaf c.i
                ((Nn (s + (e + 1))).lastVersion c.i) ins = o := ⟨_, rfl⟩
            rw [hout] at h1n hdiv hf hs hhalf hwh ⊢
            rw [hdiv] at hhalf
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
              (fun h0 hnr => by rw [h1top]; exact hR0 h0 hnr)
              (by
                intro z zn h
                rw [hN1] at h
                by_cases hz2 : z = w.next
                · rw [hz2, updN_self] at h; cases h; exact hwh.2
                · rw [updN_ne _ _ _ _ hz2] at h
                  by_cases hz1 : z = X (s + (e + 1))
                  · rw [hz1, updN_self] at h; cases h; exact hwh.1
                  · rw [updN_ne _ _ _ _ hz1] at h; exact hW z zn h)
              (by rw [h1top]; exact hT2)
            refine writerWP_mono hpar ?_
            rintro _ w2 ⟨hT2', ⟨h2top, h2t, h2path, h2next, h2vals⟩, h2frame, h2reach, h2W, h2R, h2ab⟩
            refine ⟨hT2', ⟨?_, by rw [h2t, h1t], by rw [h2path, h1path], by omega,
              by rw [h2vals, h1vals]⟩, ?_, ?_, h2W, ?_, ?_⟩
            rotate_left 4
            · intro z hz
              rw [h2ab z hz, h1n]
              have h1' : ¬ z = X (s + (e + 1)) := by omega
              have h2' : ¬ z = w.next := by omega
              simp only [h1', h2', ↓reduceIte]
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
            · intro Val hVal key
              rw [h2R Val (fun z hz => hVal z (by
                rcases hz with h | ⟨i, h1, h2, h3⟩
                · exact Or.inl (by omega)
                · exact Or.inr ⟨i, h1, by omega, h3⟩)) key, h1top]
              have hXqj : X (s + (e + 1)) ≠ X (s + e) := fun h => hqx h.symm
              have hXjn : X (s + (e + 1)) ≠ w.next := by omega
              exact getFromR_spaceInPlaceLevel _ _ Val c.i c.p.fuel w.top.rootKey (X (s + e))
                (X (s + (e + 1))) w.next (Nn (s + e)) _ out.1 out.2.1 (K (s + (e + 1))) r.1 hV hwfV hVq
                hrqV hql' hqwf hqtimes hkl hqx hrK.1
                (fun c' z hcz => by
                  by_cases hle : c' ≤ K (s + (e + 1))
                  · exact Or.inl hle
                  · exact Or.inr (hrK.2 c' z hcz (by omega)))
                (updN_self _ _ _) (hVfr w.next (Nat.le_refl _))
                (fun u c' z hu hl h => by
                  subst h; exact hVfresh _ (Nat.le_refl _) u c' (reachS_tReach _ _ _ _ hu) hl)
                (by rw [updN_ne _ _ _ _ hXqj, hN1, updN_ne _ _ _ _ hXjn, updN_self])
                (by rw [updN_ne _ _ _ _ (hQn w.next (Nat.le_refl _)), hN1, updN_self])
                hhalf.1 hhalf.2.1 hhalf.2.2.1 hhalf.2.2.2.1 hhalf.2.2.2.2.1 hhalf.2.2.2.2.2
                (updN_self _ _ _)
                (by
                  intro z h1 h2 h3
                  rw [updN_ne _ _ _ _ h2, hN1, updN_ne _ _ _ _ h3, updN_ne _ _ _ _ h1,
                    updN_ne _ _ _ _ h1])
                hrootX (hrootN w.next (Nat.le_refl _)) key
        · by_cases hqlf : (Nn (s + e)).leaf = true
          · -- a space split below a leaf: left out (hspace)
            exfalso
            have h := (hspace (s + (e + 1)) (by omega) hD hNR hsp).2
            have he : s + (e + 1) - 1 = s + e := by omega
            rw [he, hqlf] at h
            cases h
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
/-- `writerWP_appendKlongs_chainGRV` for the writer's values. -/
theorem writerWP_appendKlongs_chainGR (c : Ctx) (base : View BVal)
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
    (hdist : ∀ i i', s ≤ i → i ≤ D → s ≤ i' → i' ≤ D → X i = X i' → i = i')
    (hspace : ∀ i, s ≤ i → i ≤ D → ¬ ChainRoom c (Nn i) →
      c.p.splitAbove < ((Nn i).lastVersion c.i).size → s < i ∧ (Nn (i - 1)).leaf = false) :
    ∀ e, s + e ≤ D → ∀ (w : W) (ins : List (Nat × NodeId)),
      InsOK (Nn (s + e)) ins → (∀ q ∈ ins, q.2 < w.next) →
      w.path = path0 →
      (∀ i, s ≤ i → i ≤ s + e → w.nodes.lookup (X i) = some (Nn i) ∧ w.taken.contains (X i) = false) →
      TreeOK (wNode c.p base w) c.i w.top.rootKey →
      (∀ i, s ≤ i → i ≤ s + e → TReach (wNode c.p base w) c.i w.top.rootKey (X i)) →
      (∀ z, w.next ≤ z → w.nodes.lookup z = none ∧ w.taken.contains z = false ∧
        knodeOf c.p base z = none) →
      (∀ u c' z, TLink (wNode c.p base w) c.i u c' z → z < w.next) →
      (s = 0 → ¬ ChainRoom c (Nn 0) → w.top.rootKey = X 0) →
      (∀ z zn, wNode c.p base w z = some zn → klongsWf zn.ks = true) →
      (∀ z, (w.next ≤ z ∨ ∃ i, s ≤ i ∧ i ≤ s + e ∧ z = X i) → wValue base w z = none) →
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
        (∀ z zn, wNode c.p base w' z = some zn → klongsWf zn.ks = true) ∧
        (∀ key, getFromR (wNode c.p base w') (wValue base w') c.i c.p.fuel key w'.top.rootKey =
          getFromR (updN (wNode c.p base w) (X (s + e))
            (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + e)))) (wValue base w) c.i
            c.p.fuel key w.top.rootKey)) := by
  intro e hle w ins h1 h2 h3 h4 h5 h6 h7 h8 h9 hW hVal hV
  refine writerWP_mono (writerWP_appendKlongs_chainGRV c base path0 s D X K Nn hX hK hlinkK hrange
    hlen hwf htimes htop hdist hspace e hle w ins h1 h2 h3 h4 h5 h6 h7 h8 h9 hW hV) ?_
  rintro _ w' ⟨hT, hb, hf, hr, hW', hR, _⟩
  refine ⟨hT, hb, hf, fun z hz => (hr z hz).imp id (fun h => h.1), hW', fun key => ?_⟩
  have hv : wValue base w' = wValue base w := by
    funext a; simp only [wValue, hb.2.1, hb.2.2.2.2]
  rw [hv]; exact hR _ hVal key

end SIS.Tree
