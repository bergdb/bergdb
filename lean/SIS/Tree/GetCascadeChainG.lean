import SIS.Tree.WriterTreeChainG
import SIS.Tree.GetCascadeIP
import SIS.Tree.GetCascadeChain
import SIS.Tree.GetNewRoot
import SIS.Tree.GetReachBack

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

/-- Every live klong of the node with the klongs put is in a half: below the
divider in the first, from it in the second (by its local compare value). -/
theorem halves_cover (t : Time) (n : KNode) (ins : List (Nat × NodeId)) (hins : InsOK n ins)
    (h2 : 2 ≤ n.live.length) (hnt : ∀ s, Klong.time s ∈ n.ks → s ≤ t) (hnwf : klongsWf n.ks = true)
    (c : Nat) (z : NodeId)
    (hc : (c, z) ∈ (ins.foldl (fun n (cv, y) => n.add t (.key cv y)) n).liveAt t) :
    (c < (halves n.leaf t (n.lastVersion t) ins).2.2 →
      ∃ c', (c', z) ∈ (halves n.leaf t (n.lastVersion t) ins).1.liveAt t) ∧
    ((halves n.leaf t (n.lastVersion t) ins).2.2 ≤ c →
      ∃ c', (c', z) ∈ (halves n.leaf t (n.lastVersion t) ins).2.1.liveAt t) := by
  have hh := halves_read t n ins hins h2 hnt hnwf
  have hwh := halves_newKlongs_wf n.leaf t n.live ins
  rw [← KNode.lastVersion_eq_newKlongs] at hwh
  have hxwf := KNode.addKeys_wf t ins n hnwf
  have hxt := KNode.addKeys_times t ins n hnt
  have hlk : (ins.foldl (fun n (cv, y) => n.add t (.key cv y)) n).live.lookup c = some z := by
    rw [KNode.liveAt_of_times _ t hxt] at hc
    exact lookup_of_mem_nodup _ (KNode.live_keys_nodup _) c z hc
  cases hl : (ins.foldl (fun n (cv, y) => n.add t (.key cv y)) n).leaf with
  | true =>
    have hxe := KNode.searchEq_live _ t hxwf hxt c
    rw [hlk] at hxe
    refine ⟨fun hlt => ?_, fun hge => ?_⟩
    · have he := hh.2.2.1 hl c hlt
      rw [hxe] at he
      cases hF : (halves n.leaf t (n.lastVersion t) ins).1.searchEq t c with
      | none => rw [hF] at he; cases he
      | some fd =>
        rw [hF] at he
        simp only [Option.map_some, Option.some.injEq] at he
        exact ⟨c, he ▸ KNode.searchEq_mem _ t c fd hwh.1 hF⟩
    · have he := hh.2.2.2.1 hl c hge
      rw [hxe] at he
      cases hS : (halves n.leaf t (n.lastVersion t) ins).2.1.searchEq t c with
      | none => rw [hS] at he; cases he
      | some fd =>
        rw [hS] at he
        simp only [Option.map_some, Option.some.injEq] at he
        exact ⟨c, he ▸ KNode.searchEq_mem _ t c fd hwh.2 hS⟩
  | false =>
    have hxe := KNode.searchLte_of_live _ t hxt c z hc
    refine ⟨fun hlt => ?_, fun hge => ?_⟩
    · have he := hh.2.2.2.2.1 hl c hlt
      rw [hxe] at he
      cases hF : (halves n.leaf t (n.lastVersion t) ins).1.searchLte t c with
      | none => rw [hF] at he; cases he
      | some fd =>
        rw [hF] at he
        simp only [Option.map_some, Option.some.injEq] at he
        exact ⟨fd.c, he ▸ KNode.searchLte_mem _ t c fd hF⟩
    · have he := hh.2.2.2.2.2 hl c hge
      rw [hxe] at he
      cases hS : (halves n.leaf t (n.lastVersion t) ins).2.1.searchLte t c with
      | none => rw [hS] at he; cases he
      | some fd =>
        rw [hS] at he
        simp only [Option.map_some, Option.some.injEq] at he
        exact ⟨fd.c, he ▸ KNode.searchLte_mem _ t c fd hS⟩

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
reached was reached in that tree or is new. The reading, for every value
lookup without values at the new ids and the chain's nodes, is that tree's, when
every path inside one segment tree of the state after is shorter than the fuel
(`SegFits`) or the space root does not space split. Generalizes
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
      c.p.splitAbove < ((Nn i).lastVersion c.i).size → i = 0 ∨ (s < i ∧ ((Nn (i - 1)).leaf = false ∨
        ((Nn i).firstTime ≠ some c.i ∧ ∀ i', s < i' → i' < i → ChainOrd c K Nn i')))) :
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
          (SegFits (wNode c.p base w') c.i (c.p.fuel - 1) w'.top.rootKey ∨
            ChainNoNewRoot c Nn s (s + e)) →
          ∀ key, getFromR (wNode c.p base w') Val c.i c.p.fuel key w'.top.rootKey =
          getFromR (updN (wNode c.p base w) (X (s + e))
            (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + e)))) Val c.i c.p.fuel key
            w.top.rootKey) ∧
          (∀ z, w'.next ≤ z → w'.nodes.lookup z = w.nodes.lookup z) ∧
          ((∀ i, s < i → i ≤ (s + e) → ChainOrd c K Nn i) →
           ∀ z, TReach (updN (wNode c.p base w) (X (s + e))
            (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + e)))) c.i w.top.rootKey z →
            (∀ i, s ≤ i → i ≤ (s + e) → z ≠ X i) → TReach (wNode c.p base w') c.i w'.top.rootKey z) ∧
          ((∀ i, s < i → i ≤ (s + e) → ChainOrd c K Nn i) →
            (∀ i, s ≤ i → i ≤ (s + e) → TReach (wNode c.p base w') c.i w'.top.rootKey (X i) ∨
              w'.nodes.lookup (X i) = some ((Nn i).toPrev (c.i - 1))) ∧
            (∀ z, w.next ≤ z → (w'.nodes.lookup z).isSome = true →
              TReach (wNode c.p base w') c.i w'.top.rootKey z))) := by
  -- the room case at any level
  have hroomCase : ∀ e, s + e ≤ D → ∀ (w : W) (ins : List (Nat × NodeId)),
      w.nodes.lookup (X (s + e)) = some (Nn (s + e)) → w.taken.contains (X (s + e)) = false →
      (Nn (s + e)).size + ins.length + 1 ≤ c.p.M →
      deadOver c.p (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + e))) = false →
      (∀ z zn, wNode c.p base w z = some zn → klongsWf zn.ks = true) → X (s + e) < w.next →
      TreeOK (updN (wNode c.p base w) (X (s + e))
        (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + e)))) c.i w.top.rootKey →
      (∀ i, s ≤ i → i ≤ s + e → TReach (updN (wNode c.p base w) (X (s + e))
        (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + e)))) c.i w.top.rootKey (X i)) →
      (∀ z, w.next ≤ z → w.nodes.lookup z = none) →
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
          (SegFits (wNode c.p base w') c.i (c.p.fuel - 1) w'.top.rootKey ∨
            ChainNoNewRoot c Nn s (s + e)) →
          ∀ key, getFromR (wNode c.p base w') Val c.i c.p.fuel key w'.top.rootKey =
          getFromR (updN (wNode c.p base w) (X (s + e))
            (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + e)))) Val c.i c.p.fuel key
            w.top.rootKey) ∧
          (∀ z, w'.next ≤ z → w'.nodes.lookup z = w.nodes.lookup z) ∧
          ((∀ i, s < i → i ≤ (s + e) → ChainOrd c K Nn i) →
           ∀ z, TReach (updN (wNode c.p base w) (X (s + e))
            (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + e)))) c.i w.top.rootKey z →
            (∀ i, s ≤ i → i ≤ (s + e) → z ≠ X i) → TReach (wNode c.p base w') c.i w'.top.rootKey z) ∧
          ((∀ i, s < i → i ≤ (s + e) → ChainOrd c K Nn i) →
            (∀ i, s ≤ i → i ≤ (s + e) → TReach (wNode c.p base w') c.i w'.top.rootKey (X i) ∨
              w'.nodes.lookup (X i) = some ((Nn i).toPrev (c.i - 1))) ∧
            (∀ z, w.next ≤ z → (w'.nodes.lookup z).isSome = true →
              TReach (wNode c.p base w') c.i w'.top.rootKey z))) := by
    intro e _ w ins hlk htk hroom hdead hW hXn hV hanc' hfr'
    refine writerWP_mono (writerWP_appendKlongs_addKeys (s + e) (X (s + e)) (Nn (s + e)) ins c w hlk
      hroom hdead) ?_
    intro _ w' hw'
    subst hw'
    have hN := wNode_upsert_updN c.p base w { w with nodes := upsert w.nodes (X (s + e)) (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + e))) } (X (s + e)) _ rfl rfl htk
    refine ⟨?_, ⟨Or.inl rfl, rfl, rfl, Nat.le_refl _, rfl⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    rotate_right 2
    · intro _ z hz _
      rw [hN]; exact hz
    · intro _
      refine ⟨fun i h1 h2 => Or.inl ?_, fun z hz h => ?_⟩
      · rw [hN]; exact hanc' i h1 h2
      · exfalso
        have hzX : ¬ z = X (s + e) := by omega
        change ((upsert w.nodes _ _).lookup z).isSome = true at h
        simp only [lookup_upsert, hzX, ↓reduceIte, hfr' z hz, Option.isSome_none,
          Bool.false_eq_true] at h
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
    · intro Val _ _ key
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
        (fun i h1 h2 => by
          have : i = s + 0 := by omega
          subst this
          exact tReach_updN_self _ c.i _ _ _ hS3 (hS4 _ (by omega) (by omega)))
        (fun z hz => (hS5 z hz).1)
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
              (SegFits (wNode c.p base w') c.i (c.p.fuel - 1) w'.top.rootKey ∨
                ChainNoNewRoot c Nn 0 0) →
              ∀ key, getFromR (wNode c.p base w') Val c.i c.p.fuel key w'.top.rootKey =
              getFromR (updN (wNode c.p base w) (X 0)
                (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn 0))) Val c.i c.p.fuel key
                w.top.rootKey) ∧
              (∀ z, w'.next ≤ z → w'.nodes.lookup z = w.nodes.lookup z) ∧
              ((∀ i, 0 < i → i ≤ 0 → ChainOrd c K Nn i) →
               ∀ z, TReach (updN (wNode c.p base w) (X 0)
                (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn 0))) c.i w.top.rootKey z →
                (∀ i, 0 ≤ i → i ≤ 0 → z ≠ X i) → TReach (wNode c.p base w') c.i w'.top.rootKey z) ∧
              ((∀ i, 0 < i → i ≤ 0 → ChainOrd c K Nn i) →
                (∀ i, 0 ≤ i → i ≤ 0 → TReach (wNode c.p base w') c.i w'.top.rootKey (X i) ∨
                  w'.nodes.lookup (X i) = some ((Nn i).toPrev (c.i - 1))) ∧
                (∀ z, w.next ≤ z → (w'.nodes.lookup z).isSome = true →
                  TReach (wNode c.p base w') c.i w'.top.rootKey z))) := by
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
            ?_, ?_, ?_, ?_, ?_⟩
          rotate_left 4
          · intro z hz
            rw [h'n, lookup_upsert]
            have : z ≠ X 0 := by omega
            simp only [this, ↓reduceIte]
          rotate_left
          · intro _
            refine ⟨fun i h1 h2 => Or.inl ?_, fun z hz h => ?_⟩
            · have : i = 0 := by omega
              subst this
              rw [h'top, hrk]; exact TReach.root
            · exfalso
              have hzX : ¬ z = X 0 := by omega
              rw [h'n, lookup_upsert] at h
              simp only [hzX, ↓reduceIte, (hS5 z hz).1, Option.isSome_none, Bool.false_eq_true] at h
          rotate_right
          · intro _ z hz hzX
            rw [hN', h'top]
            rw [hrk] at hz ⊢
            refine tReach_transport _ _ c.i (X 0) (X 0) (X 0) _ (updN_self _ _ _) ?_ ?_ ?_ z hz (hzX 0 (Nat.le_refl _) (Nat.le_refl _))
            · exact (fun h => absurd rfl h)
            · exact (fun u c' z' _ hux _ hl _ => by
                obtain ⟨mm, hm, hc⟩ := hl
                rw [updN_ne _ _ _ _ hux] at hm
                exact ⟨mm, by rw [updN_ne _ _ _ _ hux]; exact hm, hc⟩)
            · exact (fun c' z' hc => TReach.link TReach.root ⟨_, updN_self _ _ _,
                liveAt_of_lookup_eq ⟨(Nn 0).leaf, l.ks⟩ _ c.i hl_times hxv_t0 (hxv_look0 l hl_look) c' z' hc⟩)
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
          · intro Val _ _ key
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
            ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          rotate_left 4
          · intro z hz
            rw [h'n]
            have h1' : ¬ z = X 0 := by omega
            have h2' : ¬ z = w.next := by omega
            simp only [h1', h2', ↓reduceIte]
          rotate_left
          · intro _
            refine ⟨fun i h1 h2 => Or.inr ?_, fun z hz h => ?_⟩
            · have : i = 0 := by omega
              subst this
              rw [h'n, if_pos rfl]
            · by_cases hzn : z = w.next
              · subst hzn; rw [h'root]; exact TReach.root
              · exfalso
                have h1' : ¬ z = X 0 := by omega
                rw [h'n] at h
                simp only [h1', hzn, ↓reduceIte, (hS5 z hz).1, Option.isSome_none,
                  Bool.false_eq_true] at h
          rotate_right
          · intro _ z hz hzX
            rw [hN', h'root]
            rw [hrk] at hz
            have hnf0 := not_reach_fresh _ c.i _ _ hV0 (hVnone w.next (Nat.le_refl _))
              (hVfresh w.next (Nat.le_refl _))
            refine tReach_transport _ _ c.i (X 0) w.next (X 0) _ (updN_self _ _ _) ?_ ?_ ?_ z hz (hzX 0 (Nat.le_refl _) (Nat.le_refl _))
            · exact (fun h => absurd rfl h)
            · exact (fun u c' z' hu hux _ hl _ => by
                obtain ⟨mm, hm, hc⟩ := hl
                have hun : u ≠ w.next := fun he => hnf0 (he ▸ hu)
                rw [updN_ne _ _ _ _ hux] at hm
                exact ⟨mm, by rw [updN_ne _ _ _ _ hun, updN_ne _ _ _ _ hux]; exact hm, hc⟩)
            · exact (fun c' z' hc => TReach.link TReach.root ⟨_, updN_self _ _ _,
                liveAt_of_lookup_eq ⟨(Nn 0).leaf, l.ks⟩ _ c.i hl_times hxv_t0 (hxv_look0 l hl_look) c' z' hc⟩)
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
          · intro Val _ _ key
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
              (SegFits (wNode c.p base w') c.i (c.p.fuel - 1) w'.top.rootKey ∨
                ChainNoNewRoot c Nn 0 0) →
              ∀ key, getFromR (wNode c.p base w') Val c.i c.p.fuel key w'.top.rootKey =
              getFromR (updN (wNode c.p base w) (X 0)
                (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn 0))) Val c.i c.p.fuel key
                w.top.rootKey) ∧
              (∀ z, w'.next ≤ z → w'.nodes.lookup z = w.nodes.lookup z) ∧
              ((∀ i, 0 < i → i ≤ 0 → ChainOrd c K Nn i) →
               ∀ z, TReach (updN (wNode c.p base w) (X 0)
                (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn 0))) c.i w.top.rootKey z →
                (∀ i, 0 ≤ i → i ≤ 0 → z ≠ X i) → TReach (wNode c.p base w') c.i w'.top.rootKey z) ∧
              ((∀ i, 0 < i → i ≤ 0 → ChainOrd c K Nn i) →
                (∀ i, 0 ≤ i → i ≤ 0 → TReach (wNode c.p base w') c.i w'.top.rootKey (X i) ∨
                  w'.nodes.lookup (X i) = some ((Nn i).toPrev (c.i - 1))) ∧
                (∀ z, w.next ≤ z → (w'.nodes.lookup z).isSome = true →
                  TReach (wNode c.p base w') c.i w'.top.rootKey z))) := by
        intro up hsp
        have h2l := hlen 0 (Nat.le_refl _) (by omega) hNR hsp
        obtain ⟨r, hdiv, hsc, _, hf, hs⟩ := chain_halves_facts c.i (Nn 0) ins hins h2l hxtimes hxwf
        have hhalf := halves_read c.i (Nn 0) ins hins h2l hxtimes hxwf
        have hwh := halves_newKlongs_wf (Nn 0).leaf c.i (Nn 0).live ins
        rw [← KNode.lastVersion_eq_newKlongs] at hwh
        have hV0wf : ∀ z zn, ReachS (updN (wNode c.p base w) (X 0)
            (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn 0))) c.i (X 0) z →
            (updN (wNode c.p base w) (X 0) (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn 0))) z =
              some zn → klongsWf zn.ks = true := fun z zn _ h => hwfV0 z zn h
        have hnoReachFresh : ∀ z, w.next ≤ z → ¬ ReachS (updN (wNode c.p base w) (X 0)
            (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn 0))) c.i (X 0) z := by
          intro z hz h
          exact not_reach_fresh _ c.i _ _ hV0 (hVnone z hz) (hVfresh z hz) (reachS_tReach _ _ _ _ h)
        have hnoxV : ∀ z zn c', ReachS (updN (wNode c.p base w) (X 0)
            (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn 0))) c.i (X 0) z →
            (updN (wNode c.p base w) (X 0) (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn 0))) z =
              some zn → (c', X 0) ∉ zn.liveAt c.i :=
          fun z zn c' hz hzn hc => hV0.rootFree z c' (reachS_tReach _ _ _ _ hz) ⟨zn, hzn, hc⟩
        have hfuel4 : 2 ≤ c.p.fuel := by unfold Params.fuel; omega
        by_cases hmade : (Nn 0).firstTime = some c.i
        · -- the root space split in place: the second half and a new root
          refine writerWP_mono (writerWP_handleFullWith_rootSpaceInPlace_term up (X 0) (Nn 0) ins c w
            hlk hmade hsp hXlt0 hfree2) ?_
          rintro _ w' ⟨h't, h'root, h'v, h'path, h'next, h'n⟩
          obtain ⟨out, hout⟩ : ∃ o, halves (Nn 0).leaf c.i ((Nn 0).lastVersion c.i) ins = o :=
            ⟨_, rfl⟩
          rw [hout] at h'n hdiv hf hs hhalf hwh
          rw [hdiv] at h'n hhalf
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
          refine ⟨by rw [h'root]; exact hT', ⟨Or.inr ⟨rfl, by omega⟩, h't, h'path, by omega, h'v⟩,
            ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
          · intro z zn h
            rw [hw'] at h
            by_cases h1 : z = X 0
            · subst h1; simp only [↓reduceIte, Option.some.injEq] at h; subst h; exact hwh.1
            · by_cases h2 : z = w.next
              · subst h2; simp only [hFx, ↓reduceIte, Option.some.injEq] at h; subst h; exact hwh.2
              · by_cases h3 : z = w.next + 2
                · subst h3; simp only [hRx, hRF, ↓reduceIte, Option.some.injEq] at h; subst h
                  exact klongsWf_newKlongs c.i [(0, X 0), (r.1, w.next)]
                · simp only [h1, h2, h3, ↓reduceIte] at h; exact hW z zn h
          · intro Val _ hfit key
            have hfitA : SegDepthLe (wNode c.p base w') c.i (c.p.fuel - 1) (w.next + 2) := by
              rcases hfit with hf' | hf'
              · rw [h'root] at hf'; exact hf' _ ReachS.root
              · exact absurd ⟨rfl, hNR, hsp⟩ hf'.1
            rw [h'root, hrk]
            exact getFromR_newRootRead _ (wNode c.p base w') Val c.i c.p.fuel (X 0) (X 0) w.next
              (w.next + 2) _ out.1 out.2.1 r.1 (updN_self _ _ _)
              (by rw [hw']; simp only [hRx, hRF, ↓reduceIte]; rfl)
              (by rw [hw']; simp only [↓reduceIte])
              (by rw [hw']; simp only [hFx, ↓reduceIte])
              hhalf.1 hhalf.2.1 hhalf.2.2.1 hhalf.2.2.2.1 hhalf.2.2.2.2.1 hhalf.2.2.2.2.2 hV0wf
              (by
                intro z hz hzx
                have h2 : ¬ z = w.next := fun h => hnoReachFresh w.next (Nat.le_refl _) (h ▸ hz)
                have h3 : ¬ z = w.next + 2 := fun h => hnoReachFresh (w.next + 2) (by omega) (h ▸ hz)
                rw [hw']
                simp only [hzx, h2, h3, ↓reduceIte]
                exact (updN_ne _ _ _ _ hzx).symm)
              hnoxV hfitA hfuel4 key
          · intro z hz
            rw [h'n]
            have h1' : ¬ z = X 0 := by omega
            have h2' : ¬ z = w.next := by omega
            have h3' : ¬ z = w.next + 2 := by omega
            simp only [h1', h2', h3', ↓reduceIte]
          · intro _ z hz hzX
            rw [h'root]
            rw [hrk] at hz
            have hcov := halves_cover c.i (Nn 0) ins hins h2l hxtimes hxwf
            rw [hout] at hcov
            rw [hdiv] at hcov
            have hRoot := rootPair_liveAt c.i (X 0) w.next r.1 hsc
            have hYF : TReach (wNode c.p base w') c.i (w.next + 2) (X 0) :=
              TReach.link TReach.root ⟨_, by rw [hw']; simp only [hRx, hRF, ↓reduceIte]; rfl, hRoot.1⟩
            have hYS : TReach (wNode c.p base w') c.i (w.next + 2) w.next :=
              TReach.link TReach.root ⟨_, by rw [hw']; simp only [hRx, hRF, ↓reduceIte]; rfl, hRoot.2⟩
            refine tReach_transport _ _ c.i (X 0) (w.next + 2) (X 0) _ (updN_self _ _ _) ?_ ?_ ?_ z hz (hzX 0 (Nat.le_refl _) (Nat.le_refl _))
            · exact (fun h => absurd rfl h)
            · exact (fun u c' z' hu hux _ hl _ => by
                obtain ⟨mm, hm, hc⟩ := hl
                have h2 : u ≠ w.next := fun h =>
                  hnoReachFresh w.next (Nat.le_refl _) (h ▸ tReach_reachS _ _ _ _ hu)
                have h3 : u ≠ w.next + 2 := fun h =>
                  hnoReachFresh (w.next + 2) (by omega) (h ▸ tReach_reachS _ _ _ _ hu)
                rw [updN_ne _ _ _ _ hux] at hm
                refine ⟨mm, ?_, hc⟩
                rw [hw']; simp only [hux, h2, h3, ↓reduceIte]; exact hm)
            · exact (fun c' z' hc => by
                obtain ⟨hF, hS⟩ := hcov c' z' hc
                by_cases hlt : c' < r.1
                · obtain ⟨c'', h''⟩ := hF hlt
                  exact TReach.link hYF ⟨out.1, by rw [hw']; simp only [↓reduceIte], h''⟩
                · obtain ⟨c'', h''⟩ := hS (by omega)
                  exact TReach.link hYS ⟨out.2.1, by rw [hw']; simp only [hFx, ↓reduceIte], h''⟩)
          · intro _
            have hYF : TReach (wNode c.p base w') c.i (w.next + 2) (X 0) :=
              TReach.link TReach.root ⟨_, by rw [hw']; simp only [hRx, hRF, ↓reduceIte]; rfl,
                (rootPair_liveAt c.i (X 0) w.next r.1 hsc).1⟩
            have hYS : TReach (wNode c.p base w') c.i (w.next + 2) w.next :=
              TReach.link TReach.root ⟨_, by rw [hw']; simp only [hRx, hRF, ↓reduceIte]; rfl,
                (rootPair_liveAt c.i (X 0) w.next r.1 hsc).2⟩
            refine ⟨fun i h1 h2 => Or.inl ?_, fun z hz h => ?_⟩
            · have : i = 0 := by omega
              subst this
              rw [h'root]; exact hYF
            · rw [h'root]
              have h1' : ¬ z = X 0 := by omega
              by_cases h2' : z = w.next
              · subst h2'; exact hYS
              · by_cases h3' : z = w.next + 2
                · subst h3'; exact TReach.root
                · exfalso
                  rw [h'n] at h
                  simp only [h1', h2', h3', ↓reduceIte, (hS5 z hz).1, Option.isSome_none,
                    Bool.false_eq_true] at h
        · -- the root space split: the halves and a new root
          refine writerWP_mono (writerWP_handleFullWith_rootSpace_term up (X 0) (Nn 0) ins c w
            hlk hmade hsp hXlt0) ?_
          rintro _ w' ⟨h't, h'root, h'v, h'path, h'next, h'n⟩
          obtain ⟨out, hout⟩ : ∃ o, halves (Nn 0).leaf c.i ((Nn 0).lastVersion c.i) ins = o :=
            ⟨_, rfl⟩
          rw [hout] at h'n hdiv hf hs hhalf hwh
          rw [hdiv] at h'n hhalf
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
          refine ⟨by rw [h'root]; exact hT', ⟨Or.inr ⟨rfl, by omega⟩, h't, h'path, by omega, h'v⟩,
            ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
          · intro z zn h
            rw [hw'] at h
            by_cases h1 : z = X 0
            · subst h1; simp only [↓reduceIte, Option.some.injEq] at h; subst h
              exact KNode.toPrev_wf _ _ hxwf
            · by_cases h2 : z = w.next
              · subst h2; simp only [hFx, ↓reduceIte, Option.some.injEq] at h; subst h; exact hwh.1
              · by_cases h3 : z = w.next + 2
                · subst h3; simp only [hSx, hSF, ↓reduceIte, Option.some.injEq] at h; subst h
                  exact hwh.2
                · by_cases h4 : z = w.next + 2 + 2
                  · subst h4; simp only [hRx, hRF, hRS, ↓reduceIte, Option.some.injEq] at h; subst h
                    exact klongsWf_newKlongs c.i [(0, w.next), (r.1, w.next + 2)]
                  · simp only [h1, h2, h3, h4, ↓reduceIte] at h; exact hW z zn h
          · intro Val _ hfit key
            have hfitA : SegDepthLe (wNode c.p base w') c.i (c.p.fuel - 1) (w.next + 2 + 2) := by
              rcases hfit with hf' | hf'
              · rw [h'root] at hf'; exact hf' _ ReachS.root
              · exact absurd ⟨rfl, hNR, hsp⟩ hf'.1
            rw [h'root, hrk]
            exact getFromR_newRootRead _ (wNode c.p base w') Val c.i c.p.fuel (X 0) w.next (w.next + 2)
              (w.next + 2 + 2) _ out.1 out.2.1 r.1 (updN_self _ _ _)
              (by rw [hw']; simp only [hRx, hRF, hRS, ↓reduceIte]; rfl)
              (by rw [hw']; simp only [hFx, ↓reduceIte])
              (by rw [hw']; simp only [hSx, hSF, ↓reduceIte])
              hhalf.1 hhalf.2.1 hhalf.2.2.1 hhalf.2.2.2.1 hhalf.2.2.2.2.1 hhalf.2.2.2.2.2 hV0wf
              (by
                intro z hz hzx
                have h2 : ¬ z = w.next := fun h => hnoReachFresh w.next (Nat.le_refl _) (h ▸ hz)
                have h3 : ¬ z = w.next + 2 := fun h => hnoReachFresh (w.next + 2) (by omega) (h ▸ hz)
                have h4 : ¬ z = w.next + 2 + 2 := fun h => hnoReachFresh (w.next + 2 + 2) (by omega) (h ▸ hz)
                rw [hw']
                simp only [hzx, h2, h3, h4, ↓reduceIte]
                exact (updN_ne _ _ _ _ hzx).symm)
              hnoxV hfitA hfuel4 key
          · intro z hz
            rw [h'n]
            have h1' : ¬ z = X 0 := by omega
            have h2' : ¬ z = w.next := by omega
            have h3' : ¬ z = w.next + 2 := by omega
            have h4' : ¬ z = w.next + 2 + 2 := by omega
            simp only [h1', h2', h3', h4', ↓reduceIte]
          · intro _ z hz hzX
            rw [h'root]
            rw [hrk] at hz
            have hcov := halves_cover c.i (Nn 0) ins hins h2l hxtimes hxwf
            rw [hout] at hcov
            rw [hdiv] at hcov
            have hRoot := rootPair_liveAt c.i w.next (w.next + 2) r.1 hsc
            have hYF : TReach (wNode c.p base w') c.i (w.next + 2 + 2) w.next :=
              TReach.link TReach.root ⟨_, by rw [hw']; simp only [hRx, hRF, hRS, ↓reduceIte]; rfl,
                hRoot.1⟩
            have hYS : TReach (wNode c.p base w') c.i (w.next + 2 + 2) (w.next + 2) :=
              TReach.link TReach.root ⟨_, by rw [hw']; simp only [hRx, hRF, hRS, ↓reduceIte]; rfl,
                hRoot.2⟩
            refine tReach_transport _ _ c.i (X 0) (w.next + 2 + 2) (X 0) _ (updN_self _ _ _) ?_ ?_ ?_ z hz (hzX 0 (Nat.le_refl _) (Nat.le_refl _))
            · exact (fun h => absurd rfl h)
            · exact (fun u c' z' hu hux _ hl _ => by
                obtain ⟨mm, hm, hc⟩ := hl
                have h2 : u ≠ w.next := fun h =>
                  hnoReachFresh w.next (Nat.le_refl _) (h ▸ tReach_reachS _ _ _ _ hu)
                have h3 : u ≠ w.next + 2 := fun h =>
                  hnoReachFresh (w.next + 2) (by omega) (h ▸ tReach_reachS _ _ _ _ hu)
                have h4 : u ≠ w.next + 2 + 2 := fun h =>
                  hnoReachFresh (w.next + 2 + 2) (by omega) (h ▸ tReach_reachS _ _ _ _ hu)
                rw [updN_ne _ _ _ _ hux] at hm
                refine ⟨mm, ?_, hc⟩
                rw [hw']; simp only [hux, h2, h3, h4, ↓reduceIte]; exact hm)
            · exact (fun c' z' hc => by
                obtain ⟨hF, hS⟩ := hcov c' z' hc
                by_cases hlt : c' < r.1
                · obtain ⟨c'', h''⟩ := hF hlt
                  exact TReach.link hYF ⟨out.1, by rw [hw']; simp only [hFx, ↓reduceIte], h''⟩
                · obtain ⟨c'', h''⟩ := hS (by omega)
                  exact TReach.link hYS ⟨out.2.1, by rw [hw']; simp only [hSx, hSF, ↓reduceIte], h''⟩)
          · intro _
            have hYF : TReach (wNode c.p base w') c.i (w.next + 2 + 2) w.next :=
              TReach.link TReach.root ⟨_, by rw [hw']; simp only [hRx, hRF, hRS, ↓reduceIte]; rfl,
                (rootPair_liveAt c.i w.next (w.next + 2) r.1 hsc).1⟩
            have hYS : TReach (wNode c.p base w') c.i (w.next + 2 + 2) (w.next + 2) :=
              TReach.link TReach.root ⟨_, by rw [hw']; simp only [hRx, hRF, hRS, ↓reduceIte]; rfl,
                (rootPair_liveAt c.i w.next (w.next + 2) r.1 hsc).2⟩
            refine ⟨fun i h1 h2 => Or.inr ?_, fun z hz h => ?_⟩
            · have : i = 0 := by omega
              subst this
              rw [h'n, if_pos rfl]
            · rw [h'root]
              have h1' : ¬ z = X 0 := by omega
              by_cases h2' : z = w.next
              · subst h2'; exact hYF
              · by_cases h3' : z = w.next + 2
                · subst h3'; exact hYS
                · by_cases h4' : z = w.next + 2 + 2
                  · subst h4'; exact TReach.root
                  · exfalso
                    rw [h'n] at h
                    simp only [h1', h2', h3', h4', ↓reduceIte, (hS5 z hz).1, Option.isSome_none,
                      Bool.false_eq_true] at h
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
        (fun i h1 h2 => by
          rcases Nat.lt_or_ge i (s + (e + 1)) with hlt | hge
          · exact chain_anc_reach (wNode c.p base w) c.i w.top.rootKey X s (s + (e + 1)) hS3
              (hS4 s (Nat.le_refl _) (by omega))
              (fun i' h1' h2' => by
                obtain ⟨a, b⟩ := hS2 (i' - 1) (by omega) (by omega)
                exact ⟨K i', Nn (i' - 1), by simp only [wNode, b, Bool.false_eq_true, ↓reduceIte, a],
                  hlinkK i' h1' (by omega)⟩) _ i h1 hlt
          · have : i = s + (e + 1) := by omega
            subst this
            exact tReach_updN_self _ c.i _ _ _ hS3 (hS4 _ (by omega) (Nat.le_refl _)))
        (fun z hz => (hS5 z hz).1)
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
      have hVlt : ∀ u, TReach (updN (wNode c.p base w) (X (s + (e + 1)))
          (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + (e + 1))))) c.i w.top.rootKey u →
          u < w.next := by
        intro u hu
        rcases Nat.lt_or_ge u w.next with h | h
        · exact h
        · exact absurd hu (not_reach_fresh _ c.i _ u hV (hVfr u h) (fun u' c' hu' => hVfresh u h u' c' hu'))
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
            (((∀ i, s < i → i ≤ s + e → ChainOrd c K Nn i) → ∀ z,
                (∃ c', (c', z) ∈ (ins'.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + e))).liveAt c.i) →
                w.next ≤ z →
                SegDepthLe (updN N1 (X (s + e)) (ins'.foldl (fun n (cv, y) => n.add c.i (.key cv y))
                  (Nn (s + e)))) c.i (c.p.fuel - 1) z) ∨
              (¬ ChainRoom c (Nn (s + (e + 1))) →
                c.p.splitAbove < ((Nn (s + (e + 1))).lastVersion c.i).size → (Nn (s + e)).leaf = false)) →
            ∀ key, getFromR (updN N1 (X (s + e)) (ins'.foldl (fun n (cv, y) => n.add c.i (.key cv y))
            (Nn (s + e)))) Val c.i c.p.fuel key w.top.rootKey =
            getFromR (updN (wNode c.p base w) (X (s + (e + 1)))
              (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + (e + 1)))))
              Val c.i c.p.fuel key w.top.rootKey) →
          (∀ z, w1.next ≤ z → w1.nodes.lookup z = w.nodes.lookup z) →
          ((∀ i, s < i → i ≤ s + (e + 1) → ChainOrd c K Nn i) →
            ∀ z, TReach (updN (wNode c.p base w) (X (s + (e + 1)))
              (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + (e + 1))))) c.i w.top.rootKey z →
            z ≠ X (s + (e + 1)) →
            TReach (updN N1 (X (s + e)) (ins'.foldl (fun n (cv, y) => n.add c.i (.key cv y))
              (Nn (s + e)))) c.i w.top.rootKey z) →
          ((∀ i, s < i → i ≤ s + (e + 1) → ChainOrd c K Nn i) →
            ∀ z, w.next ≤ z → z < w1.next → (w1.nodes.lookup z).isSome = true →
            TReach (updN N1 (X (s + e)) (ins'.foldl (fun n (cv, y) => n.add c.i (.key cv y))
              (Nn (s + e)))) c.i w.top.rootKey z) →
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
                (SegFits (wNode c.p base w3) c.i (c.p.fuel - 1) w3.top.rootKey ∨
                  ChainNoNewRoot c Nn s (s + (e + 1))) →
                ∀ key, getFromR (wNode c.p base w3) Val c.i c.p.fuel key w3.top.rootKey =
                getFromR (updN (wNode c.p base w) (X (s + (e + 1)))
                  (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + (e + 1))))) Val c.i c.p.fuel key
                  w.top.rootKey) ∧
                (∀ z, w3.next ≤ z → w3.nodes.lookup z = w.nodes.lookup z) ∧
                ((∀ i, s < i → i ≤ (s + (e + 1)) → ChainOrd c K Nn i) →
                 ∀ z, TReach (updN (wNode c.p base w) (X (s + (e + 1)))
                  (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + (e + 1))))) c.i w.top.rootKey z →
                  (∀ i, s ≤ i → i ≤ (s + (e + 1)) → z ≠ X i) → TReach (wNode c.p base w3) c.i w3.top.rootKey z) ∧
                ((∀ i, s < i → i ≤ (s + (e + 1)) → ChainOrd c K Nn i) →
                  (∀ i, s ≤ i → i ≤ (s + (e + 1)) → TReach (wNode c.p base w3) c.i w3.top.rootKey (X i) ∨
                    w3.nodes.lookup (X i) = some ((Nn i).toPrev (c.i - 1))) ∧
                  (∀ z, w.next ≤ z → (w3.nodes.lookup z).isSome = true →
                    TReach (wNode c.p base w3) c.i w3.top.rootKey z)))) := by
        intro w1 ins' N1 New hins' hinsT' h1path h1t h1top h1next h1vals hNew h1low hN1 hT1 hR1 hS5' hS6' hV1 hRV1 hW1 hlev hab1 hRBs hNewR
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
        rintro _ w2 ⟨hT2, ⟨h2top, h2t, h2path, h2next, h2vals⟩, h2frame, h2reach, h2W, h2R, h2ab, h2RB,
          h2RN⟩
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
        refine ⟨?_, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
        · intro hHS z hz hzX
          have hz1 := hRBs hHS z hz (hzX _ (by omega) (Nat.le_refl _))
          have hz2 := h2RB (fun i h1 h2 => hHS i h1 (by omega)) z (by rw [hN1, h1top]; exact hz1)
            (fun i h1 h2 => hzX i h1 (by omega))
          have h3top : w3.top = w2.top := by rw [← hw3]
          rw [hN3]
          try rw [h3top]
          exact tReach_updN_keep _ c.i _ _ _ hxR2 z hz2
        · intro hHS
          obtain ⟨hR2c, hR3c⟩ := h2RN (fun i h1 h2 => hHS i h1 (by omega))
          have h3top : w3.top = w2.top := by rw [← hw3]
          refine ⟨fun i h1 h2 => ?_, fun z hz h => ?_⟩
          · rcases Nat.lt_or_ge i (s + (e + 1)) with hlt | hge
            · have hiX : ¬ X i = X (s + (e + 1)) := fun he => by
                have := hdist _ _ h1 (by omega) (by omega) hD he; omega
              rcases hR2c i h1 (by omega) with h' | h'
              · left
                rw [hN3]
                try rw [h3top]
                exact tReach_updN_keep _ c.i _ _ _ hxR2 _ h'
              · right
                try rw [h3n]
                rw [lookup_upsert, if_neg hiX]
                exact h'
            · right
              have : i = s + (e + 1) := by omega
              subst this
              try rw [h3n]
              rw [lookup_upsert, if_pos rfl]
          · have hzX : ¬ z = X (s + (e + 1)) := by
              have := hXlt (s + (e + 1)) (by omega) (Nat.le_refl _); omega
            have h2' : (w2.nodes.lookup z).isSome = true := by
              try rw [h3n] at h
              rw [lookup_upsert, if_neg hzX] at h; exact h
            rw [hN3]
            try rw [h3top]
            apply tReach_updN_keep _ c.i _ _ _ hxR2
            rcases Nat.lt_or_ge z w1.next with hlt | hge
            · have h1' : (w1.nodes.lookup z).isSome = true := by
                rw [← h2frame z hlt (fun i h1 h2 he => by have := hXlt i h1 (by omega); omega)]
                exact h2'
              have hzV := hNewR hHS z hz hlt h1'
              exact h2RB (fun i h1 h2 => hHS i h1 (by omega)) z (by rw [hN1, h1top]; exact hzV)
                (fun i h1 h2 he => by have := hXlt i h1 (by omega); omega)
            · exact hR3c z hge h2'
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
        · intro Val hVal hfit key
          have h3top : w3.top = w2.top := by rw [← hw3]
          have hfit2 : SegFits (wNode c.p base w2) c.i (c.p.fuel - 1) w2.top.rootKey ∨
              ChainNoNewRoot c Nn s (s + e) := by
            rcases hfit with hf | hf
            · left
              rw [hN3] at hf
              try rw [h3top] at hf
              exact SegFits.of_agree _ _ c.i _ _
                (fun x hx => updN_ne _ _ _ _ (fun he : x = X (s + (e + 1)) => hxR2 (he ▸ hx))) hf
            · exact Or.inr ⟨hf.1, fun i h1 h2 => hf.2 i h1 (by omega)⟩
          rw [hN3]
          try rw [h3top]
          rw [getFromR_updN_unreach' (wNode c.p base w2) Val c.i c.p.fuel w2.top.rootKey
            (X (s + (e + 1))) _ (fun z zn _ h => h2W z zn h)
            (fun h => hxR2 (reachS_tReach _ _ _ _ h)) key]
          rw [h2R Val (fun z hz => hVal z (by
            rcases hz with h | ⟨i, h1, h2, h3⟩
            · exact Or.inl (by omega)
            · exact Or.inr ⟨i, h1, by omega, h3⟩)) hfit2 key, h1top, hN1]
          refine hlev Val hVal ?_ key
          rcases hfit with hf | hf
          · left
            intro hHS z ⟨c', hc'⟩ hzn
            have hf2 : SegFits (wNode c.p base w2) c.i (c.p.fuel - 1) w2.top.rootKey := by
              rw [hN3] at hf
              try rw [h3top] at hf
              exact SegFits.of_agree _ _ c.i _ _
                (fun x hx => updN_ne _ _ _ _ (fun he : x = X (s + (e + 1)) => hxR2 (he ▸ hx))) hf
            have hqR' : TReach (updN N1 (X (s + e)) (ins'.foldl (fun n (cv, y) => n.add c.i (.key cv y))
                (Nn (s + e)))) c.i w.top.rootKey (X (s + e)) :=
              tReach_updN_self _ c.i _ _ _ hT1 (hR1 (s + e) (by omega) (Nat.le_refl _))
            have hzR := TReach.link hqR' ⟨_, updN_self _ _ _, hc'⟩
            have hz2 := h2RB hHS z (by rw [hN1, h1top]; exact hzR)
              (fun i h1 h2 he => by have := hXlt i h1 (by omega); omega)
            have hd2 := hf2 z (tReach_reachS _ _ _ _ hz2)
            refine SegDepthLe.of_agree _ _ c.i _ z ?_ hd2
            intro y hy
            have hyR : ReachS (updN N1 (X (s + e)) (ins'.foldl (fun n (cv, y) => n.add c.i (.key cv y))
                (Nn (s + e)))) c.i w.top.rootKey y :=
              reachS_trans _ c.i _ z (tReach_reachS _ _ _ _ hzR) y hy
            have hylt : y < w1.next := by
              cases hyR with
              | root =>
                have := Nat.lt_of_not_le (fun h => hrootN _ h rfl)
                omega
              | step u un c'' _ hu hun hmem =>
                by_cases hux : u = X (s + e)
                · rw [hux, updN_self] at hun
                  simp only [Option.some.injEq] at hun
                  subst hun
                  have hf' := KNode.addKeys_liveAt_fold c.i ins' _ hqwf hqtimes c'' y hmem
                  rcases pairLookupFold_some_mem c'' ins' _ y hf' with hm | hm
                  · exact hinsT' (c'', y) hm
                  · have hm' := lookup_some_mem hm
                    rw [← KNode.liveAt_of_times _ c.i hqtimes] at hm'
                    have := hS6 _ _ _ ⟨_, hwq, hm'⟩
                    omega
                · rw [updN_ne _ _ _ _ hux] at hun
                  exact hS6' u c'' y ⟨un, hun, hmem⟩
            have hyX : ∀ i, s ≤ i → i ≤ s + e → y ≠ X i := by
              intro i h1 h2 he
              have hXi : ReachS (updN N1 (X (s + e)) (ins'.foldl (fun n (cv, y) => n.add c.i (.key cv y))
                  (Nn (s + e)))) c.i (X i) z := by
                refine reachS_trans _ c.i _ (X (s + e)) ?_ z (ReachS.step _ _ c' z ReachS.root (updN_self _ _ _) hc')
                refine chain_reachS _ c.i X K Nn i (s + e) h2 ?_
                intro i' h1' h2'
                have hne : X i' ≠ X (s + e) := fun hh => by
                  have := hdist _ _ (by omega) (by omega) (by omega) (by omega) hh; omega
                refine ⟨?_, ?_⟩
                · rw [updN_ne _ _ _ _ hne, ← hN1]
                  obtain ⟨a, b⟩ := hS2 i' (by omega) (by omega)
                  simp only [wNode, h1t, b, Bool.false_eq_true, ↓reduceIte,
                    h1low _ (hXlt i' (by omega) (by omega)), a]
                · have := hlinkK (i' + 1) (by omega) (by omega)
                  simpa using this
              have := reach_antisymm _ c.i _ _ _ hV1 hzR (he ▸ hy) hXi
              have := hXlt i h1 (by omega)
              omega
            rw [updN_ne _ _ _ _ (hyX (s + e) (by omega) (Nat.le_refl _)), ← hN1]
            simp only [wNode, h2t, h2frame y hylt hyX]
          · right
            exact hf.2 (s + (e + 1)) (by omega) (Nat.le_refl _)
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
              (SegFits (wNode c.p base w') c.i (c.p.fuel - 1) w'.top.rootKey ∨
                ChainNoNewRoot c Nn s (s + (e + 1))) →
              ∀ key, getFromR (wNode c.p base w') Val c.i c.p.fuel key w'.top.rootKey =
              getFromR (updN (wNode c.p base w) (X (s + (e + 1)))
                (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + (e + 1))))) Val c.i c.p.fuel key
                w.top.rootKey) ∧
              (∀ z, w'.next ≤ z → w'.nodes.lookup z = w.nodes.lookup z) ∧
              ((∀ i, s < i → i ≤ (s + (e + 1)) → ChainOrd c K Nn i) →
               ∀ z, TReach (updN (wNode c.p base w) (X (s + (e + 1)))
                (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + (e + 1))))) c.i w.top.rootKey z →
                (∀ i, s ≤ i → i ≤ (s + (e + 1)) → z ≠ X i) → TReach (wNode c.p base w') c.i w'.top.rootKey z) ∧
              ((∀ i, s < i → i ≤ (s + (e + 1)) → ChainOrd c K Nn i) →
                (∀ i, s ≤ i → i ≤ (s + (e + 1)) → TReach (wNode c.p base w') c.i w'.top.rootKey (X i) ∨
                  w'.nodes.lookup (X i) = some ((Nn i).toPrev (c.i - 1))) ∧
                (∀ z, w.next ≤ z → (w'.nodes.lookup z).isSome = true →
                  TReach (wNode c.p base w') c.i w'.top.rootKey z))) := by
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
            intro Val hVal _
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
          (by
            intro _ z hz hzx
            have hTN1 : TreeOK (updN (wNode c.p base w) w.next ⟨(Nn (s + (e + 1))).leaf, l.ks⟩) c.i
                w.top.rootKey :=
              treeOK_updN_unreach _ c.i _ _ _ hS3 (hyR w.next (Nat.le_refl _))
            have hRq : TReach (updN (wNode c.p base w) w.next ⟨(Nn (s + (e + 1))).leaf, l.ks⟩) c.i
                w.top.rootKey (X (s + e)) := by
              obtain ⟨a, ha⟩ := (hS4 (s + e) (by omega) (by omega)).pathLen
              exact tReach_updN_of_short _ c.i _ _ _ a _ ha
                (fun b hb => absurd hb.reach (hyR w.next (Nat.le_refl _)))
            have hRq' := tReach_updN_self _ c.i _ _ ([(K (s + (e + 1)), w.next)].foldl
              (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + e))) hTN1 hRq
            have hy : TReach (updN (updN (wNode c.p base w) w.next ⟨(Nn (s + (e + 1))).leaf, l.ks⟩)
                (X (s + e)) ([(K (s + (e + 1)), w.next)].foldl (fun n (cv, y) => n.add c.i (.key cv y))
                  (Nn (s + e)))) c.i w.top.rootKey w.next :=
              TReach.link hRq' ⟨_, updN_self _ _ _, KNode.add_key_liveAt_self _ c.i _ _ hqwf hqtimes⟩
            refine tReach_transport _ _ c.i w.top.rootKey w.top.rootKey (X (s + (e + 1))) _ (updN_self _ _ _) ?_ ?_ ?_ z hz hzx
            · exact (fun _ => TReach.root)
            · exact (fun u c' z' hu hux _ hl hzx' => by
                obtain ⟨mm, hm, hc⟩ := hl
                by_cases huq : u = X (s + e)
                · subst huq
                  rw [updN_ne _ _ _ _ hqx, hwq] at hm
                  cases hm
                  exact ⟨_, updN_self _ _ _, insOK_keep c.i _ _ (Or.inl ⟨_, _, rfl⟩) (K (s + (e + 1)))
                    (fun a ha => by simp at ha; rw [← ha]) hqwf hqtimes _ hkl c' z' hc hzx'⟩
                · have hun : u ≠ w.next := by have := hVlt u hu; omega
                  rw [updN_ne _ _ _ _ hux] at hm
                  exact ⟨mm, by rw [updN_ne _ _ _ _ huq, updN_ne _ _ _ _ hun]; exact hm, hc⟩)
            · exact (fun c' z' hc => TReach.link hy ⟨⟨(Nn (s + (e + 1))).leaf, l.ks⟩, by
                  rw [updN_ne _ _ _ _ (fun h => by have := hXlt (s + e) (by omega) (by omega); omega)]
                  exact updN_self _ _ _,
                liveAt_of_lookup_eq ⟨(Nn (s + (e + 1))).leaf, l.ks⟩ _ c.i hl_times hxv_t
                  (fun c'' => by rw [KNode.addKeys_live_lookup c.i ins _ hxwf c'']; exact hl_look c'')
                  c' z' hc⟩))
          (by
            intro _ z hz hlt h
            have hzn : z = w.next := by
              refine Classical.byContradiction (fun hne => ?_)
              rw [h1n, List.lookup_append, (hS5 z hz).1] at h
              have hb : (z == w.next) = false := by simp only [beq_eq_false_iff_ne, ne_eq]; exact hne
              simp [List.lookup, hb] at h
            subst hzn
            have hTN1 : TreeOK (updN (wNode c.p base w) w.next ⟨(Nn (s + (e + 1))).leaf, l.ks⟩) c.i
                w.top.rootKey :=
              treeOK_updN_unreach _ c.i _ _ _ hS3 (hyR w.next (Nat.le_refl _))
            have hRq : TReach (updN (wNode c.p base w) w.next ⟨(Nn (s + (e + 1))).leaf, l.ks⟩) c.i
                w.top.rootKey (X (s + e)) := by
              obtain ⟨a, ha⟩ := (hS4 (s + e) (by omega) (by omega)).pathLen
              exact tReach_updN_of_short _ c.i _ _ _ a _ ha
                (fun b hb => absurd hb.reach (hyR w.next (Nat.le_refl _)))
            have hRq' := tReach_updN_self _ c.i _ _ ([(K (s + (e + 1)), w.next)].foldl
              (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + e))) hTN1 hRq
            exact TReach.link hRq' ⟨_, updN_self _ _ _, KNode.add_key_liveAt_self _ c.i _ _ hqwf hqtimes⟩)
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
              (SegFits (wNode c.p base w') c.i (c.p.fuel - 1) w'.top.rootKey ∨
                ChainNoNewRoot c Nn s (s + (e + 1))) →
              ∀ key, getFromR (wNode c.p base w') Val c.i c.p.fuel key w'.top.rootKey =
              getFromR (updN (wNode c.p base w) (X (s + (e + 1)))
                (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + (e + 1))))) Val c.i c.p.fuel key
                w.top.rootKey) ∧
              (∀ z, w'.next ≤ z → w'.nodes.lookup z = w.nodes.lookup z) ∧
              ((∀ i, s < i → i ≤ (s + (e + 1)) → ChainOrd c K Nn i) →
               ∀ z, TReach (updN (wNode c.p base w) (X (s + (e + 1)))
                (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + (e + 1))))) c.i w.top.rootKey z →
                (∀ i, s ≤ i → i ≤ (s + (e + 1)) → z ≠ X i) → TReach (wNode c.p base w') c.i w'.top.rootKey z) ∧
              ((∀ i, s < i → i ≤ (s + (e + 1)) → ChainOrd c K Nn i) →
                (∀ i, s ≤ i → i ≤ (s + (e + 1)) → TReach (wNode c.p base w') c.i w'.top.rootKey (X i) ∨
                  w'.nodes.lookup (X i) = some ((Nn i).toPrev (c.i - 1))) ∧
                (∀ z, w.next ≤ z → (w'.nodes.lookup z).isSome = true →
                  TReach (wNode c.p base w') c.i w'.top.rootKey z))) := by
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
            intro Val hVal _
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
          (by
            intro hHS z hz hzx
            have hKr := chainOrd_div c K Nn (s + (e + 1)) (hHS (s + (e + 1)) (by omega) (Nat.le_refl _))
              hNR (by simpa using hql) hsp ins hins h2l
            rw [hout, hdiv] at hKr
            have hcov := halves_cover c.i (Nn (s + (e + 1))) ins hins h2l hxtimes hxwf
            rw [hout] at hcov
            rw [hdiv] at hcov
            have hR2 : ¬ TReach (updN (wNode c.p base w) w.next out.1) c.i w.top.rootKey (w.next + 2) :=
              fun h => hyR (w.next + 2) (by omega)
                (tReach_updN_unreach _ c.i _ _ _ (hyR w.next (Nat.le_refl _)) _ h)
            have hTN1 : TreeOK (updN (updN (wNode c.p base w) w.next out.1) (w.next + 2) out.2.1) c.i
                w.top.rootKey :=
              treeOK_updN_unreach _ c.i _ _ _
                (treeOK_updN_unreach _ c.i _ _ _ hS3 (hyR w.next (Nat.le_refl _))) hR2
            have hRq : TReach (updN (updN (wNode c.p base w) w.next out.1) (w.next + 2) out.2.1) c.i
                w.top.rootKey (X (s + e)) := by
              obtain ⟨a, ha⟩ := (hS4 (s + e) (by omega) (by omega)).pathLen
              have h1r := tReach_updN_of_short _ c.i _ _ out.1 a _ ha
                (fun b hb => absurd hb.reach (hyR w.next (Nat.le_refl _)))
              obtain ⟨a', ha'⟩ := h1r.pathLen
              exact tReach_updN_of_short _ c.i _ _ _ a' _ ha' (fun b hb => absurd hb.reach hR2)
            have hRq' := tReach_updN_self _ c.i _ _ ([(K (s + (e + 1)), w.next), (r.1, w.next + 2)].foldl
              (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + e))) hTN1 hRq
            have hmemF : (K (s + (e + 1)), w.next) ∈ ([(K (s + (e + 1)), w.next), (r.1, w.next + 2)].foldl
                (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + e))).liveAt c.i := by
              apply KNode.addKeys_liveAt_of_fold c.i _ _ hqwf hqtimes
              have hne : (r.1 == K (s + (e + 1))) = false := by
                simp only [beq_eq_false_iff_ne, ne_eq]; omega
              simp [pairLookupStep, hne]
            have hmemS : (r.1, w.next + 2) ∈ ([(K (s + (e + 1)), w.next), (r.1, w.next + 2)].foldl
                (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + e))).liveAt c.i := by
              apply KNode.addKeys_liveAt_of_fold c.i _ _ hqwf hqtimes
              simp [pairLookupStep]
            have hF := TReach.link hRq' ⟨_, updN_self _ _ _, hmemF⟩
            have hS := TReach.link hRq' ⟨_, updN_self _ _ _, hmemS⟩
            refine tReach_transport _ _ c.i w.top.rootKey w.top.rootKey (X (s + (e + 1))) _ (updN_self _ _ _) ?_ ?_ ?_ z hz hzx
            · exact (fun _ => TReach.root)
            · exact (fun u c' z' hu hux _ hl hzx' => by
                obtain ⟨mm, hm, hc⟩ := hl
                by_cases huq : u = X (s + e)
                · subst huq
                  rw [updN_ne _ _ _ _ hqx, hwq] at hm
                  cases hm
                  exact ⟨_, updN_self _ _ _, insOK_keep c.i _ _
                    (Or.inr ⟨_, _, _, _, rfl, hrK.1, fun c'' z'' hm hlt => by
                      have := hrK.2 c'' z'' (by simpa using hm) hlt; exact this⟩)
                    (K (s + (e + 1))) (fun a ha => by simp at ha; rw [← ha]) hqwf hqtimes _ hkl c' z' hc
                    hzx'⟩
                · have hu1 : u ≠ w.next := by have := hVlt u hu; omega
                  have hu2 : u ≠ w.next + 2 := by have := hVlt u hu; omega
                  rw [updN_ne _ _ _ _ hux] at hm
                  exact ⟨mm, by rw [updN_ne _ _ _ _ huq, updN_ne _ _ _ _ hu2, updN_ne _ _ _ _ hu1]; exact hm,
                    hc⟩)
            · exact (fun c' z' hc => by
                obtain ⟨hFc, hSc⟩ := hcov c' z' hc
                by_cases hlt : c' < r.1
                · obtain ⟨c'', h''⟩ := hFc hlt
                  exact TReach.link hF ⟨out.1, by
                    rw [updN_ne _ _ _ _ (Ne.symm hQn1), updN_ne _ _ _ _ h12, updN_self], h''⟩
                · obtain ⟨c'', h''⟩ := hSc (by omega)
                  exact TReach.link hS ⟨out.2.1, by
                    rw [updN_ne _ _ _ _ (Ne.symm hQn2), updN_self], h''⟩))
          (by
            intro hHS z hz hlt h
            have hKr := chainOrd_div c K Nn (s + (e + 1)) (hHS (s + (e + 1)) (by omega) (Nat.le_refl _))
              hNR (by simpa using hql) hsp ins hins h2l
            rw [hout, hdiv] at hKr
            have hcov := halves_cover c.i (Nn (s + (e + 1))) ins hins h2l hxtimes hxwf
            rw [hout] at hcov
            rw [hdiv] at hcov
            have hR2 : ¬ TReach (updN (wNode c.p base w) w.next out.1) c.i w.top.rootKey (w.next + 2) :=
              fun h => hyR (w.next + 2) (by omega)
                (tReach_updN_unreach _ c.i _ _ _ (hyR w.next (Nat.le_refl _)) _ h)
            have hTN1 : TreeOK (updN (updN (wNode c.p base w) w.next out.1) (w.next + 2) out.2.1) c.i
                w.top.rootKey :=
              treeOK_updN_unreach _ c.i _ _ _
                (treeOK_updN_unreach _ c.i _ _ _ hS3 (hyR w.next (Nat.le_refl _))) hR2
            have hRq : TReach (updN (updN (wNode c.p base w) w.next out.1) (w.next + 2) out.2.1) c.i
                w.top.rootKey (X (s + e)) := by
              obtain ⟨a, ha⟩ := (hS4 (s + e) (by omega) (by omega)).pathLen
              have h1r := tReach_updN_of_short _ c.i _ _ out.1 a _ ha
                (fun b hb => absurd hb.reach (hyR w.next (Nat.le_refl _)))
              obtain ⟨a', ha'⟩ := h1r.pathLen
              exact tReach_updN_of_short _ c.i _ _ _ a' _ ha' (fun b hb => absurd hb.reach hR2)
            have hRq' := tReach_updN_self _ c.i _ _ ([(K (s + (e + 1)), w.next), (r.1, w.next + 2)].foldl
              (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + e))) hTN1 hRq
            have hmemF : (K (s + (e + 1)), w.next) ∈ ([(K (s + (e + 1)), w.next), (r.1, w.next + 2)].foldl
                (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + e))).liveAt c.i := by
              apply KNode.addKeys_liveAt_of_fold c.i _ _ hqwf hqtimes
              have hne : (r.1 == K (s + (e + 1))) = false := by
                simp only [beq_eq_false_iff_ne, ne_eq]; omega
              simp [pairLookupStep, hne]
            have hmemS : (r.1, w.next + 2) ∈ ([(K (s + (e + 1)), w.next), (r.1, w.next + 2)].foldl
                (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + e))).liveAt c.i := by
              apply KNode.addKeys_liveAt_of_fold c.i _ _ hqwf hqtimes
              simp [pairLookupStep]
            have hF := TReach.link hRq' ⟨_, updN_self _ _ _, hmemF⟩
            have hS := TReach.link hRq' ⟨_, updN_self _ _ _, hmemS⟩
            rw [h1n] at h
            by_cases h1' : z = w.next
            · subst h1'; exact hF
            · by_cases h2' : z = w.next + 2
              · subst h2'; exact hS
              · exfalso
                simp only [h1', h2', ↓reduceIte, (hS5 z hz).1, Option.isSome_none,
                  Bool.false_eq_true] at h)
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
              (SegFits (wNode c.p base w') c.i (c.p.fuel - 1) w'.top.rootKey ∨
                ChainNoNewRoot c Nn s (s + (e + 1))) →
              ∀ key, getFromR (wNode c.p base w') Val c.i c.p.fuel key w'.top.rootKey =
              getFromR (updN (wNode c.p base w) (X (s + (e + 1)))
                (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + (e + 1))))) Val c.i c.p.fuel key
                w.top.rootKey) ∧
              (∀ z, w'.next ≤ z → w'.nodes.lookup z = w.nodes.lookup z) ∧
              ((∀ i, s < i → i ≤ (s + (e + 1)) → ChainOrd c K Nn i) →
               ∀ z, TReach (updN (wNode c.p base w) (X (s + (e + 1)))
                (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + (e + 1))))) c.i w.top.rootKey z →
                (∀ i, s ≤ i → i ≤ (s + (e + 1)) → z ≠ X i) → TReach (wNode c.p base w') c.i w'.top.rootKey z) ∧
              ((∀ i, s < i → i ≤ (s + (e + 1)) → ChainOrd c K Nn i) →
                (∀ i, s ≤ i → i ≤ (s + (e + 1)) → TReach (wNode c.p base w') c.i w'.top.rootKey (X i) ∨
                  w'.nodes.lookup (X i) = some ((Nn i).toPrev (c.i - 1))) ∧
                (∀ z, w.next ≤ z → (w'.nodes.lookup z).isSome = true →
                  TReach (wNode c.p base w') c.i w'.top.rootKey z))) := by
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
            ?_, ?_, ?_, ?_, ?_⟩
          rotate_left 4
          · intro z hz
            have hzX : z ≠ X (s + (e + 1)) := by
              have := hXlt (s + (e + 1)) (by omega) (Nat.le_refl _); omega
            rw [h'n, lookup_upsert]
            simp only [hzX, ↓reduceIte]
          rotate_left
          · intro _
            refine ⟨fun i h1 h2 => Or.inl ?_, fun z hz h => ?_⟩
            · rw [hN', h'top]
              rcases Nat.lt_or_ge i (s + (e + 1)) with hlt | hge
              · exact hanc _ i h1 (by omega)
              · have : i = s + (e + 1) := by omega
                subst this
                exact tReach_updN_self _ c.i _ _ _ hS3 (hS4 _ (by omega) (Nat.le_refl _))
            · exfalso
              have hzX : ¬ z = X (s + (e + 1)) := by
                have := hXlt (s + (e + 1)) (by omega) (Nat.le_refl _); omega
              rw [h'n, lookup_upsert] at h
              simp only [hzX, ↓reduceIte, (hS5 z hz).1, Option.isSome_none, Bool.false_eq_true] at h
          rotate_right
          · intro _ z hz hzX
            rw [hN', h'top]
            refine tReach_transport _ _ c.i w.top.rootKey w.top.rootKey (X (s + (e + 1))) _ (updN_self _ _ _) ?_ ?_ ?_ z hz (hzX _ (by omega) (Nat.le_refl _))
            · exact (fun _ => TReach.root)
            · exact (fun u c' z' _ hux _ hl _ => by
                obtain ⟨mm, hm, hc⟩ := hl
                rw [updN_ne _ _ _ _ hux] at hm
                exact ⟨mm, by rw [updN_ne _ _ _ _ hux]; exact hm, hc⟩)
            · exact (fun c' z' hc => TReach.link
                (tReach_updN_self _ c.i _ _ _ hS3 (hS4 (s + (e + 1)) (by omega) (Nat.le_refl _)))
                ⟨_, updN_self _ _ _, liveAt_of_lookup_eq ⟨(Nn (s + (e + 1))).leaf, l.ks⟩ _ c.i hl_times hxv_t
                  (fun c'' => by rw [KNode.addKeys_live_lookup c.i ins _ hxwf c'']; exact hl_look c'')
                  c' z' hc⟩)
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
          · intro Val _ _ key
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
              (SegFits (wNode c.p base w') c.i (c.p.fuel - 1) w'.top.rootKey ∨
                ChainNoNewRoot c Nn s (s + (e + 1))) →
              ∀ key, getFromR (wNode c.p base w') Val c.i c.p.fuel key w'.top.rootKey =
              getFromR (updN (wNode c.p base w) (X (s + (e + 1)))
                (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + (e + 1))))) Val c.i c.p.fuel key
                w.top.rootKey) ∧
              (∀ z, w'.next ≤ z → w'.nodes.lookup z = w.nodes.lookup z) ∧
              ((∀ i, s < i → i ≤ (s + (e + 1)) → ChainOrd c K Nn i) →
               ∀ z, TReach (updN (wNode c.p base w) (X (s + (e + 1)))
                (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + (e + 1))))) c.i w.top.rootKey z →
                (∀ i, s ≤ i → i ≤ (s + (e + 1)) → z ≠ X i) → TReach (wNode c.p base w') c.i w'.top.rootKey z) ∧
              ((∀ i, s < i → i ≤ (s + (e + 1)) → ChainOrd c K Nn i) →
                (∀ i, s ≤ i → i ≤ (s + (e + 1)) → TReach (wNode c.p base w') c.i w'.top.rootKey (X i) ∨
                  w'.nodes.lookup (X i) = some ((Nn i).toPrev (c.i - 1))) ∧
                (∀ z, w.next ≤ z → (w'.nodes.lookup z).isSome = true →
                  TReach (wNode c.p base w') c.i w'.top.rootKey z))) := by
        intro hsp
        by_cases hmade : (Nn (s + (e + 1))).firstTime = some c.i
        · by_cases hqlf : (Nn (s + e)).leaf = true
          · -- a space split in place below a leaf: left out (hspace)
            exfalso
            have h := ((hspace (s + (e + 1)) (by omega) hD hNR hsp).resolve_left (by omega)).2
            have he : s + (e + 1) - 1 = s + e := by omega
            rw [he, hqlf] at h
            rcases h with h | h
            · cases h
            · exact h.1 hmade
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
            rintro _ w2 ⟨hT2', ⟨h2top, h2t, h2path, h2next, h2vals⟩, h2frame, h2reach, h2W, h2R, h2ab,
              h2RB, h2RN⟩
            refine ⟨hT2', ⟨?_, by rw [h2t, h1t], by rw [h2path, h1path], by omega,
              by rw [h2vals, h1vals]⟩, ?_, ?_, h2W, ?_, ?_, ?_, ?_⟩
            rotate_left 4
            · intro z hz
              rw [h2ab z hz, h1n]
              have h1' : ¬ z = X (s + (e + 1)) := by omega
              have h2' : ¬ z = w.next := by omega
              simp only [h1', h2', ↓reduceIte]
            · intro hHS z hz hzx
              have hKr := chainOrd_div c K Nn (s + (e + 1)) (hHS (s + (e + 1)) (by omega) (Nat.le_refl _))
                hNR (by simpa using hql') hsp ins hins h2l
              rw [hout, hdiv] at hKr
              have hcov := halves_cover c.i (Nn (s + (e + 1))) ins hins h2l hxtimes hxwf
              rw [hout] at hcov
              rw [hdiv] at hcov
              have hXjn : X (s + (e + 1)) ≠ w.next := by omega
              have hRq : TReach (updN (updN (wNode c.p base w) (X (s + (e + 1))) out.1) w.next out.2.1) c.i
                  w.top.rootKey (X (s + e)) :=
                tReach_to_agree _ _ c.i _ hagree1 _ (hanc out.1 (s + e) (by omega) (by omega))
              have hRq' := tReach_updN_self _ c.i _ _ ([(r.1, w.next)].foldl
                (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + e))) hT1 hRq
              have hne : ∀ c' z', (c', z') ∈ (Nn (s + e)).liveAt c.i → z' ≠ X (s + (e + 1)) → r.1 ≠ c' := by
                intro c' z' hc hz' he
                subst he
                rcases Nat.lt_or_ge (K (s + (e + 1))) r.1 with h | h
                · have := hrK.2 r.1 z' (by
                    have h' := hc; rw [KNode.liveAt_of_times _ c.i hqtimes] at h'; simpa using h') h
                  omega
                · omega
              have hmemX : (K (s + (e + 1)), X (s + (e + 1))) ∈ ([(r.1, w.next)].foldl
                  (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + e))).liveAt c.i :=
                addKeys_liveAt_keep c.i _ _ hqwf hqtimes _ _ hkl (fun q hq => by
                  simp only [List.mem_singleton] at hq; subst hq; simp only; omega)
              have hmemS : (r.1, w.next) ∈ ([(r.1, w.next)].foldl
                  (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + e))).liveAt c.i :=
                KNode.add_key_liveAt_self _ c.i _ _ hqwf hqtimes
              have hXr := TReach.link hRq' ⟨_, updN_self _ _ _, hmemX⟩
              have hSr := TReach.link hRq' ⟨_, updN_self _ _ _, hmemS⟩
              have hz1 : TReach (updN (updN (updN (wNode c.p base w) (X (s + (e + 1))) out.1) w.next out.2.1)
                  (X (s + e)) ([(r.1, w.next)].foldl (fun n (cv, y) => n.add c.i (.key cv y))
                    (Nn (s + e)))) c.i w.top.rootKey z :=
                tReach_transport _ _ c.i w.top.rootKey w.top.rootKey (X (s + (e + 1))) _ (updN_self _ _ _)
                  (fun _ => TReach.root)
                  (fun u c' z' hu hux _ hl hzx' => by
                    obtain ⟨mm, hm, hc⟩ := hl
                    by_cases huq : u = X (s + e)
                    · subst huq
                      rw [updN_ne _ _ _ _ hqx, hwq] at hm
                      cases hm
                      exact ⟨_, updN_self _ _ _, addKeys_liveAt_keep c.i _ _ hqwf hqtimes _ _ hc
                        (fun q hq => by
                          simp only [List.mem_singleton] at hq; subst hq; exact hne c' z' hc hzx')⟩
                    · have hu1 : u ≠ w.next := by have := hVlt u hu; omega
                      rw [updN_ne _ _ _ _ hux] at hm
                      refine ⟨mm, ?_, hc⟩
                      rw [updN_ne _ _ _ _ huq, updN_ne _ _ _ _ hu1, updN_ne _ _ _ _ hux]
                      exact hm)
                  (fun c' z' hc => by
                    obtain ⟨hFc, hSc⟩ := hcov c' z' hc
                    by_cases hlt : c' < r.1
                    · obtain ⟨c'', h''⟩ := hFc hlt
                      exact TReach.link hXr ⟨out.1, by
                        rw [updN_ne _ _ _ _ (Ne.symm hqx), updN_ne _ _ _ _ hXjn, updN_self], h''⟩
                    · obtain ⟨c'', h''⟩ := hSc (by omega)
                      exact TReach.link hSr ⟨out.2.1, by
                        rw [updN_ne _ _ _ _ (hQn w.next (Nat.le_refl _)), updN_self], h''⟩)
                  z hz (hzx _ (by omega) (Nat.le_refl _))
              exact h2RB (fun i h1 h2 => hHS i h1 (by omega)) z (by rw [hN1, h1top]; exact hz1)
                (fun i h1 h2 => hzx i h1 (by omega))
            · intro hHS
              have hKr := chainOrd_div c K Nn (s + (e + 1)) (hHS (s + (e + 1)) (by omega) (Nat.le_refl _))
                hNR (by simpa using hql') hsp ins hins h2l
              rw [hout, hdiv] at hKr
              have hcov := halves_cover c.i (Nn (s + (e + 1))) ins hins h2l hxtimes hxwf
              rw [hout] at hcov
              rw [hdiv] at hcov
              have hXjn : X (s + (e + 1)) ≠ w.next := by omega
              have hRq : TReach (updN (updN (wNode c.p base w) (X (s + (e + 1))) out.1) w.next out.2.1) c.i
                  w.top.rootKey (X (s + e)) :=
                tReach_to_agree _ _ c.i _ hagree1 _ (hanc out.1 (s + e) (by omega) (by omega))
              have hRq' := tReach_updN_self _ c.i _ _ ([(r.1, w.next)].foldl
                (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + e))) hT1 hRq
              have hne : ∀ c' z', (c', z') ∈ (Nn (s + e)).liveAt c.i → z' ≠ X (s + (e + 1)) → r.1 ≠ c' := by
                intro c' z' hc hz' he
                subst he
                rcases Nat.lt_or_ge (K (s + (e + 1))) r.1 with h | h
                · have := hrK.2 r.1 z' (by
                    have h' := hc; rw [KNode.liveAt_of_times _ c.i hqtimes] at h'; simpa using h') h
                  omega
                · omega
              have hmemX : (K (s + (e + 1)), X (s + (e + 1))) ∈ ([(r.1, w.next)].foldl
                  (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + e))).liveAt c.i :=
                addKeys_liveAt_keep c.i _ _ hqwf hqtimes _ _ hkl (fun q hq => by
                  simp only [List.mem_singleton] at hq; subst hq; simp only; omega)
              have hmemS : (r.1, w.next) ∈ ([(r.1, w.next)].foldl
                  (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + e))).liveAt c.i :=
                KNode.add_key_liveAt_self _ c.i _ _ hqwf hqtimes
              have hXr := TReach.link hRq' ⟨_, updN_self _ _ _, hmemX⟩
              have hSr := TReach.link hRq' ⟨_, updN_self _ _ _, hmemS⟩
              obtain ⟨hR2c, hR3c⟩ := h2RN (fun i h1 h2 => hHS i h1 (by omega))
              refine ⟨fun i h1 h2 => ?_, fun z hz h => ?_⟩
              · rcases Nat.lt_or_ge i (s + (e + 1)) with hlt | hge
                · exact hR2c i h1 (by omega)
                · left
                  have : i = s + (e + 1) := by omega
                  subst this
                  exact h2RB (fun i h1 h2 => hHS i h1 (by omega)) _ (by rw [hN1, h1top]; exact hXr)
                    (fun i h1 h2 he => by have := hdist _ _ h1 (by omega) (by omega) hD he.symm; omega)
              · rcases Nat.lt_or_ge z w1.next with hlt | hge
                · have hzX : ¬ z = X (s + (e + 1)) := by omega
                  have h1' : (w1.nodes.lookup z).isSome = true := by
                    rw [← h2frame z hlt (fun i h1 h2 he => by have := hXlt i h1 (by omega); omega)]
                    exact h
                  have hzn : z = w.next := by
                    refine Classical.byContradiction (fun hne => ?_)
                    rw [h1n] at h1'
                    simp only [hzX, hne, ↓reduceIte, (hS5 z hz).1, Option.isSome_none,
                      Bool.false_eq_true] at h1'
                  subst hzn
                  exact h2RB (fun i h1 h2 => hHS i h1 (by omega)) _ (by rw [hN1, h1top]; exact hSr)
                    (fun i h1 h2 he => by have := hXlt i h1 (by omega); omega)
                · exact hR3c z hge h
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
            · intro Val hVal hfit key
              rw [h2R Val (fun z hz => hVal z (by
                rcases hz with h | ⟨i, h1, h2, h3⟩
                · exact Or.inl (by omega)
                · exact Or.inr ⟨i, h1, by omega, h3⟩))
                (hfit.imp id (fun hf => ⟨hf.1, fun i h1 h2 => hf.2 i h1 (by omega)⟩)) key, h1top]
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
          · -- a space split below a leaf, the node not made: a new segment root above the halves
            have hseg := ((hspace (s + (e + 1)) (by omega) hD hNR hsp).resolve_left (by omega)).2
            have he1 : s + (e + 1) - 1 = s + e := by omega
            rw [he1, hqlf] at hseg
            have hord : ∀ i', s < i' → i' < s + (e + 1) → ChainOrd c K Nn i' := by
              rcases hseg with h | h
              · cases h
              · exact h.2
            have hfuel4 : 2 ≤ c.p.fuel := by unfold Params.fuel; omega
            have h2l := hlen (s + (e + 1)) (by omega) hD hNR hsp
            obtain ⟨r, hdiv, hsc, _, hf, hs⟩ := chain_halves_facts c.i (Nn (s + (e + 1))) ins hins h2l
              hxtimes hxwf
            have hhalf := halves_read c.i (Nn (s + (e + 1))) ins hins h2l hxtimes hxwf
            have hwh := halves_newKlongs_wf (Nn (s + (e + 1))).leaf c.i (Nn (s + (e + 1))).live ins
            rw [← KNode.lastVersion_eq_newKlongs] at hwh
            have hcov := halves_cover c.i (Nn (s + (e + 1))) ins hins h2l hxtimes hxwf
            apply writerWP_handleFullWith_segSpace_up (s + e) (X (s + (e + 1))) (X (s + e))
              (Nn (s + (e + 1))) (Nn (s + e)) (K (s + (e + 1))) ins c w hlk hlq hqlf hmade hsp hpq hpk
            intro w1 h1n h1t h1top h1path h1next h1vals
            obtain ⟨out, hout⟩ : ∃ o, halves (Nn (s + (e + 1))).leaf c.i
                ((Nn (s + (e + 1))).lastVersion c.i) ins = o := ⟨_, rfl⟩
            rw [hout] at h1n hdiv hf hs hhalf hwh hcov
            rw [hdiv] at h1n hhalf hcov
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
              (by
                intro z zn h
                rw [hN1] at h
                by_cases hz3 : z = w.next + 2 + 2
                · rw [hz3, updN_self] at h; cases h
                  exact klongsWf_newKlongs c.i [(0, w.next), (r.1, w.next + 2)]
                · rw [updN_ne _ _ _ _ hz3] at h
                  by_cases hz2 : z = w.next + 2
                  · rw [hz2, updN_self] at h; cases h; exact hwh.2
                  · rw [updN_ne _ _ _ _ hz2] at h
                    by_cases hz1 : z = w.next
                    · rw [hz1, updN_self] at h; cases h; exact hwh.1
                    · rw [updN_ne _ _ _ _ hz1] at h; exact hW z zn h)
              (by
                intro Val hVal hHF key
                rcases hHF with hHF | hNo
                · have hdR := hHF (fun i' h1 h2 => hord i' h1 (by omega)) (w.next + 2 + 2)
                    ⟨K (s + (e + 1)), KNode.add_key_liveAt_self _ c.i _ _ hqwf hqtimes⟩ (by omega)
                  exact getFromR_segSpaceLevel _ _ Val c.i c.p.fuel hfuel4 w.top.rootKey (X (s + e))
                    (X (s + (e + 1))) w.next (w.next + 2) (w.next + 2 + 2) (Nn (s + e)) _ out.1 out.2.1
                    (K (s + (e + 1))) r.1 hV hwfV hVq hrqV hqlf hqwf hqtimes hkl hqx (updN_self _ _ _)
                    (hVfr w.next (Nat.le_refl _)) (hVfr (w.next + 2) (by omega))
                    (hVfr (w.next + 2 + 2) (by omega))
                    (fun u c' z hu hl => ⟨fun h => hVfresh w.next (Nat.le_refl _) u c'
                        (reachS_tReach _ _ _ _ hu) (h ▸ hl),
                      fun h => hVfresh (w.next + 2) (by omega) u c' (reachS_tReach _ _ _ _ hu) (h ▸ hl),
                      fun h => hVfresh (w.next + 2 + 2) (by omega) u c' (reachS_tReach _ _ _ _ hu)
                        (h ▸ hl)⟩)
                    (by rw [updN_ne _ _ _ _ (hQn _ (by omega)), hN1, updN_self]; rfl)
                    (by
                      rw [updN_ne _ _ _ _ (hQn _ (Nat.le_refl _)), hN1,
                        updN_ne _ _ _ _ (by omega : w.next ≠ w.next + 2 + 2),
                        updN_ne _ _ _ _ (by omega : w.next ≠ w.next + 2), updN_self])
                    (by
                      rw [updN_ne _ _ _ _ (hQn _ (by omega)), hN1,
                        updN_ne _ _ _ _ (by omega : w.next + 2 ≠ w.next + 2 + 2), updN_self])
                    hhalf.1 hhalf.2.1 hhalf.2.2.1 hhalf.2.2.2.1 hhalf.2.2.2.2.1 hhalf.2.2.2.2.2
                    (updN_self _ _ _)
                    (by
                      intro z hz1 hz2 hz3 hz4 hz5
                      rw [updN_ne _ _ _ _ hz2, hN1, updN_ne _ _ _ _ hz5, updN_ne _ _ _ _ hz4,
                        updN_ne _ _ _ _ hz3]
                      exact (updN_ne _ _ _ _ hz1).symm)
                    (hvalx Val hVal _ (by omega)) (hrootN _ (by omega)) hrootX (hrootN _ (Nat.le_refl _))
                    (hrootN _ (by omega)) hdR key
                · exact absurd (hNo hNR hsp) (by rw [hqlf]; simp))
              (by
                intro z hz
                rw [h1next] at hz
                rw [h1n]
                have h1' : ¬ z = w.next := by omega
                have h2' : ¬ z = w.next + 2 := by omega
                have h3' : ¬ z = w.next + 2 + 2 := by omega
                simp only [h1', h2', h3', ↓reduceIte])
              (by
                intro _ z hz hzx
                have hqR' := tReach_updN_self _ c.i _ _ ([(K (s + (e + 1)), w.next + 2 + 2)].foldl
                  (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + e)))
                  (treeOK_of_agree _ _ _ _ hS3 hagree)
                  (tReach_to_agree _ _ _ _ hagree _ (hS4 (s + e) (by omega) (by omega)))
                have hR' := TReach.link hqR' ⟨_, updN_self _ _ _,
                  KNode.add_key_liveAt_self _ c.i _ _ hqwf hqtimes⟩
                have hRoot := rootPair_liveAt c.i w.next (w.next + 2) r.1 hsc
                have hRn : (updN (wNode c.p base w1) (X (s + e)) ([(K (s + (e + 1)), w.next + 2 + 2)].foldl
                    (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + e)))) (w.next + 2 + 2) =
                    some ⟨false, newKlongs c.i [(0, w.next), (r.1, w.next + 2)]⟩ := by
                  rw [updN_ne _ _ _ _ (hQn _ (by omega)), hN1, updN_self]; rfl
                have hFr := TReach.link hR' ⟨_, hRn, hRoot.1⟩
                have hSr := TReach.link hR' ⟨_, hRn, hRoot.2⟩
                refine tReach_transport _ _ c.i w.top.rootKey w.top.rootKey (X (s + (e + 1))) _
                  (updN_self _ _ _) ?_ ?_ ?_ z hz hzx
                · exact (fun _ => TReach.root)
                · intro u c' z' hu hux _ hl hzx'
                  obtain ⟨mm, hm, hc⟩ := hl
                  by_cases huq : u = X (s + e)
                  · subst huq
                    rw [updN_ne _ _ _ _ hqx, hwq] at hm
                    cases hm
                    exact ⟨_, updN_self _ _ _, insOK_keep c.i _ _ (Or.inl ⟨_, _, rfl⟩) (K (s + (e + 1)))
                      (fun a ha => by simp at ha; rw [← ha]) hqwf hqtimes _ hkl c' z' hc hzx'⟩
                  · have hu0 := hVlt u hu
                    rw [updN_ne _ _ _ _ hux] at hm
                    refine ⟨mm, ?_, hc⟩
                    rw [updN_ne _ _ _ _ huq, wNode_low_agree c.p base w w1 h1t h1low u hu0]
                    exact hm
                · intro c' z' hc
                  obtain ⟨hFc, hSc⟩ := hcov c' z' hc
                  by_cases hlt : c' < r.1
                  · obtain ⟨c'', h''⟩ := hFc hlt
                    exact TReach.link hFr ⟨out.1, by
                      rw [updN_ne _ _ _ _ (hQn _ (Nat.le_refl _)), hN1,
                        updN_ne _ _ _ _ (by omega : w.next ≠ w.next + 2 + 2),
                        updN_ne _ _ _ _ (by omega : w.next ≠ w.next + 2), updN_self], h''⟩
                  · obtain ⟨c'', h''⟩ := hSc (by omega)
                    exact TReach.link hSr ⟨out.2.1, by
                      rw [updN_ne _ _ _ _ (hQn _ (by omega)), hN1,
                        updN_ne _ _ _ _ (by omega : w.next + 2 ≠ w.next + 2 + 2), updN_self], h''⟩)
              (by
                intro _ z hz hlt h
                have hqR' := tReach_updN_self _ c.i _ _ ([(K (s + (e + 1)), w.next + 2 + 2)].foldl
                  (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + e)))
                  (treeOK_of_agree _ _ _ _ hS3 hagree)
                  (tReach_to_agree _ _ _ _ hagree _ (hS4 (s + e) (by omega) (by omega)))
                have hR' := TReach.link hqR' ⟨_, updN_self _ _ _,
                  KNode.add_key_liveAt_self _ c.i _ _ hqwf hqtimes⟩
                have hRoot := rootPair_liveAt c.i w.next (w.next + 2) r.1 hsc
                have hRn : (updN (wNode c.p base w1) (X (s + e)) ([(K (s + (e + 1)), w.next + 2 + 2)].foldl
                    (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + e)))) (w.next + 2 + 2) =
                    some ⟨false, newKlongs c.i [(0, w.next), (r.1, w.next + 2)]⟩ := by
                  rw [updN_ne _ _ _ _ (hQn _ (by omega)), hN1, updN_self]; rfl
                have hFr := TReach.link hR' ⟨_, hRn, hRoot.1⟩
                have hSr := TReach.link hR' ⟨_, hRn, hRoot.2⟩
                rw [h1n] at h
                by_cases h1' : z = w.next
                · subst h1'; exact hFr
                · by_cases h2' : z = w.next + 2
                  · subst h2'; exact hSr
                  · by_cases h3' : z = w.next + 2 + 2
                    · subst h3'; exact hR'
                    · exfalso
                      simp only [h1', h2', h3', ↓reduceIte, (hS5 z hz).1, Option.isSome_none,
                        Bool.false_eq_true] at h)
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
/-- The cascade keeps what the tree reached (`writerWP_appendKlongs_chainGRV`'s
last conjunct): every node that the tree with the klongs put into X (s + e)
reaches, but the chain's nodes, is reached after the cascade, when the nodes
that space split below an inner parent have their compare values in their
ranges (`ChainOrd`, which `RangeOrder` gives). -/
theorem writerWP_appendKlongs_chainReach (c : Ctx) (base : View BVal)
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
      c.p.splitAbove < ((Nn i).lastVersion c.i).size → i = 0 ∨ (s < i ∧ ((Nn (i - 1)).leaf = false ∨
        ((Nn i).firstTime ≠ some c.i ∧ ∀ i', s < i' → i' < i → ChainOrd c K Nn i')))) :
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
        (∀ i, s < i → i ≤ s + e → ChainOrd c K Nn i) →
        ∀ z, TReach (updN (wNode c.p base w) (X (s + e))
          (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + e)))) c.i w.top.rootKey z →
        (∀ i, s ≤ i → i ≤ s + e → z ≠ X i) → TReach (wNode c.p base w') c.i w'.top.rootKey z) := by
  intro e hle w ins h1 h2 h3 h4 h5 h6 h7 h8 h9 hW hV
  exact writerWP_mono (writerWP_appendKlongs_chainGRV c base path0 s D X K Nn hX hK hlinkK hrange
    hlen hwf htimes htop hdist hspace e hle w ins h1 h2 h3 h4 h5 h6 h7 h8 h9 hW hV)
    (fun _ _ h => h.2.2.2.2.2.2.2.1)

/-- The cascade's chain nodes and new nodes after it (`writerWP_appendKlongs_chainGRV`'s
last conjunct): every chain node is reached, or it holds its version before the
transaction (`toPrev`, a split that is not in place left it behind); every node
the cascade made is reached; given `ChainOrd`. -/
theorem writerWP_appendKlongs_chainReachNew (c : Ctx) (base : View BVal)
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
      c.p.splitAbove < ((Nn i).lastVersion c.i).size → i = 0 ∨ (s < i ∧ ((Nn (i - 1)).leaf = false ∨
        ((Nn i).firstTime ≠ some c.i ∧ ∀ i', s < i' → i' < i → ChainOrd c K Nn i')))) :
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
        (∀ i, s < i → i ≤ s + e → ChainOrd c K Nn i) →
        (∀ i, s ≤ i → i ≤ s + e → TReach (wNode c.p base w') c.i w'.top.rootKey (X i) ∨
          w'.nodes.lookup (X i) = some ((Nn i).toPrev (c.i - 1))) ∧
        (∀ z, w.next ≤ z → (w'.nodes.lookup z).isSome = true →
          TReach (wNode c.p base w') c.i w'.top.rootKey z)) := by
  intro e hle w ins h1 h2 h3 h4 h5 h6 h7 h8 h9 hW hV
  exact writerWP_mono (writerWP_appendKlongs_chainGRV c base path0 s D X K Nn hX hK hlinkK hrange
    hlen hwf htimes htop hdist hspace e hle w ins h1 h2 h3 h4 h5 h6 h7 h8 h9 hW hV)
    (fun _ _ h => h.2.2.2.2.2.2.2.2)

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
    hlen hwf htimes htop hdist (fun i h1 h2 h3 h4 => Or.inr ⟨(hspace i h1 h2 h3 h4).1,
      Or.inl (hspace i h1 h2 h3 h4).2⟩) e hle w ins h1 h2 h3
    h4 h5 h6 h7 h8 h9 hW hV) ?_
  rintro _ w' ⟨hT, hb, hf, hr, hW', hR, _⟩
  refine ⟨hT, hb, hf, fun z hz => (hr z hz).imp id (fun h => h.1), hW', fun key => ?_⟩
  have hv : wValue base w' = wValue base w := by
    funext a; simp only [wValue, hb.2.1, hb.2.2.2.2]
  rw [hv]
  exact hR _ hVal (Or.inr ⟨fun ⟨h0, hnr, hsp⟩ => by
    have := (hspace 0 (by omega) (by omega) hnr hsp).1
    omega, fun i h1 h2 hnr hsp => (hspace i (by omega) (by omega) hnr hsp).2⟩) key

/-- `writerWP_appendKlongs_chainGRV` for the writer's values, the space root's
space split allowed: the reading holds when every path inside one segment tree
of the state after is shorter than the fuel (`SegFits`) or the chain does not
reach a space root that space splits. -/
theorem writerWP_appendKlongs_chainGRQ (c : Ctx) (base : View BVal)
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
      c.p.splitAbove < ((Nn i).lastVersion c.i).size → i = 0 ∨ (s < i ∧ ((Nn (i - 1)).leaf = false ∨
        ((Nn i).firstTime ≠ some c.i ∧ ∀ i', s < i' → i' < i → ChainOrd c K Nn i')))) :
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
        ((SegFits (wNode c.p base w') c.i (c.p.fuel - 1) w'.top.rootKey ∨
            ChainNoNewRoot c Nn s (s + e)) →
          ∀ key, getFromR (wNode c.p base w') (wValue base w') c.i c.p.fuel key w'.top.rootKey =
          getFromR (updN (wNode c.p base w) (X (s + e))
            (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + e)))) (wValue base w) c.i
            c.p.fuel key w.top.rootKey) ∧
        ((∀ i, s < i → i ≤ s + e → ChainOrd c K Nn i) →
          ∀ z, TReach (updN (wNode c.p base w) (X (s + e))
            (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + e)))) c.i w.top.rootKey z →
          (∀ i, s ≤ i → i ≤ s + e → z ≠ X i) → TReach (wNode c.p base w') c.i w'.top.rootKey z) ∧
        ((∀ i, s < i → i ≤ (s + e) → ChainOrd c K Nn i) →
          (∀ i, s ≤ i → i ≤ (s + e) → TReach (wNode c.p base w') c.i w'.top.rootKey (X i) ∨
            w'.nodes.lookup (X i) = some ((Nn i).toPrev (c.i - 1))) ∧
          (∀ z, w.next ≤ z → (w'.nodes.lookup z).isSome = true →
            TReach (wNode c.p base w') c.i w'.top.rootKey z))) := by
  intro e hle w ins h1 h2 h3 h4 h5 h6 h7 h8 h9 hW hVal hV
  refine writerWP_mono (writerWP_appendKlongs_chainGRV c base path0 s D X K Nn hX hK hlinkK hrange
    hlen hwf htimes htop hdist hspace e hle w ins h1 h2 h3 h4 h5 h6 h7 h8 h9 hW hV) ?_
  rintro _ w' ⟨hT, hb, hf, hr, hW', hR, _, hRB, hRN⟩
  refine ⟨hT, hb, hf, fun z hz => (hr z hz).imp id (fun h => h.1), hW', fun hq key => ?_, hRB, hRN⟩
  have hv : wValue base w' = wValue base w := by
    funext a; simp only [wValue, hb.2.1, hb.2.2.2.2]
  rw [hv]
  exact hR _ hVal hq key

end SIS.Tree
