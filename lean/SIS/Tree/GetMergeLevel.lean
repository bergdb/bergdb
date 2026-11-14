/-
The merge's full parent at any depth (bergdb 024-22): `handleFull` of a last
version given, at depth D + 1 of the key access path below the cascade's nodes
X s .. X D, in all its kinds: a time split or a space split, in place for a node
that the transaction made or not, below an inner node or a segment leaf
(`writerWP_handleFull_lastV`; `writerWP_handleFull_lastVF` leaves out the space
split in place below a segment leaf by its `hspaceL`). The writer's tree after it is a tree and
reads as the tree with the node's content replaced by the last version
(`writerWP_appendKlongs_chainGRV`'s step at its top level, for a last version
with nothing put).
-/
import SIS.Tree.HalvesNil
import SIS.Tree.WGetAt
import SIS.Tree.WriterTreeDelChain
import SIS.Tree.GetCascadePut

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- The split of the merge's full parent at depth D + 1 makes no new segment
root: a space split is below an inner node. -/
def LevelNoRoot (c : Ctx) (Nn : Nat → KNode) (D : Nat) (last : KNode) (compact : Bool) : Prop :=
  (!compact && decide (last.size > c.p.splitAbove)) = true → (Nn D).leaf = false

/-- The facts of the halves of a node whose last version is itself, with nothing
put: the divider r, a live klong, the halves' links below it and from it. -/
theorem halves_facts_nil (t : Time) (n : KNode) (h2 : 2 ≤ n.live.length)
    (hnt : ∀ s, Klong.time s ∈ n.ks → s ≤ t) :
    ∃ r : Nat × NodeId, (halves n.leaf t (n.lastVersion t) []).2.2 = r.1 ∧ 0 < r.1 ∧ r ∈ n.live ∧
      (∀ c z, (c, z) ∈ (halves n.leaf t (n.lastVersion t) []).1.liveAt t → c < r.1 ∧
        (c, z) ∈ n.liveAt t) ∧
      (∀ c z, (c, z) ∈ (halves n.leaf t (n.lastVersion t) []).2.1.liveAt t → ∃ c0, r.1 ≤ c0 ∧
        c = splitLocalCv n.leaf r.1 c0 ∧ (c0, z) ∈ n.liveAt t) := by
  obtain ⟨r, hr⟩ := divider_exists n (by omega)
  have hrm := divider_mem_live n r hr
  have hsc := divider_pos' n r h2 hr
  obtain ⟨hdiv, hfh, hsh⟩ := halves_links_nil n.leaf t n rfl r hr hsc
  have hmem : ∀ c z, n.live.lookup c = some z → (c, z) ∈ n.liveAt t := by
    intro c z h
    rw [KNode.liveAt_of_times n t hnt]
    exact mem_of_lookup_nodup _ c z h
  refine ⟨r, hdiv, hsc, hrm, fun c z h => ?_, fun c z h => ?_⟩
  · obtain ⟨h1, h2⟩ := hfh c z h
    exact ⟨h1, hmem c z h2⟩
  · obtain ⟨c0, h1, h2, h3⟩ := hsh c z h
    exact ⟨c0, h1, h2, hmem c0 z h3⟩

/-- The order of the full parent's last version below an inner parent: the
cascade's `ChainOrd` at depth D + 1 with X (D + 1)'s content replaced by
`last`. Its live compare values are at or above the parent's klong to it, and
strictly above for an inner node (but the 0 klong). -/
def LastOrd (c : Ctx) (K : Nat → Nat) (Nn : Nat → KNode) (D : Nat) (last : KNode) : Prop :=
  c.p.splitAbove < last.size → (Nn D).leaf = false →
    ∀ c' z, (c', z) ∈ (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode).live →
      if (Nn (D + 1)).leaf = true then K (D + 1) ≤ c' else (c' = 0 ∨ K (D + 1) < c')

/-- With `LastOrd`, the divider of a space split of the last version below an
inner parent is above the parent's klong to the node (`chainOrd_div`). -/
theorem lastOrd_div (c : Ctx) (K : Nat → Nat) (Nn : Nat → KNode) (D : Nat) (last : KNode)
    (hord : LastOrd c K Nn D last) (hql : (Nn D).leaf = false) (hsp : c.p.splitAbove < last.size)
    (hlastV : (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode).lastVersion c.i = last)
    (h2 : 2 ≤ (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode).live.length) :
    K (D + 1) < (halves (Nn (D + 1)).leaf c.i last []).2.2 := by
  obtain ⟨r, hr⟩ := divider_exists (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode) (by omega)
  have hrm := divider_mem_live _ r hr
  have hsc := divider_pos' _ r h2 hr
  obtain ⟨hdiv, _, _⟩ := halves_links_nil (Nn (D + 1)).leaf c.i (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode)
    rfl r hr hsc
  have hdiv' : (halves (Nn (D + 1)).leaf c.i
      ((⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode).lastVersion c.i) []).2.2 = r.1 := hdiv
  rw [hlastV] at hdiv'
  rw [hdiv']
  obtain ⟨a0, ha0, ha0r⟩ := live_below_divider' _ r h2 hr
  have hr1 := hord hsp hql r.1 r.2 hrm
  have ha1 := hord hsp hql a0.1 a0.2 ha0
  cases hl : (Nn (D + 1)).leaf with
  | true =>
    simp only [hl, ↓reduceIte] at ha1
    omega
  | false =>
    simp only [hl, Bool.false_eq_true, ↓reduceIte] at hr1
    rcases hr1 with h | h
    · omega
    · exact h

set_option maxHeartbeats 4000000 in
/-- `handleFull` of the last version `last` of the node X (D + 1), with the
cascade above it (`writerWP_appendKlongs_chainGRV` for X s .. X D, its premises
as there): given that the tree with X (D + 1)'s content replaced by `last` is a
tree (`hV`), that `last` is its own last version (`hlastV`) and names nodes
below the next id (`hvx`), the writer's tree after it is a tree whose nodes are
reached there or new, and it reads as that tree when the state after fits the
fuel or no new root is made. X (D + 1) is not reached after, or holds key klongs
of `last` only (a split in place). For a space split, `last` has two live
klongs (`hlen2`), its live compare values are in the range of its link in an
inner parent (`hrangeL`), and below a segment leaf the levels of the cascade
are ordered for a node the transaction did not make (`hspaceL`). With the
cascade's levels and `last` ordered (`ChainOrd`, `LastOrd`), the nodes reached
before, but the path's, are reached after, the path's nodes are reached after or
left as their previous versions, and the new nodes are reached. -/
theorem writerWP_handleFull_lastV (fuelR : Nat) (hfR : 2 ≤ fuelR) (c : Ctx) (base : View BVal)
    (path0 : List (Option Nat × NodeId)) (s D : Nat) (X : Nat → NodeId) (K : Nat → Nat)
    (Nn : Nat → KNode) (hsD : s ≤ D)
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
    (hspace : ∀ i, s ≤ i → i ≤ D → ¬ ChainRoom c (Nn i) →
      c.p.splitAbove < ((Nn i).lastVersion c.i).size → i = 0 ∨ (s < i ∧ ((Nn (i - 1)).leaf = false ∨
        ((Nn i).firstTime ≠ some c.i → ∀ i', s < i' → i' < i → ChainOrd c K Nn i'))))
    (last : KNode) (compact : Bool)
    (hlwf : klongsWf last.ks = true) (hlt : ∀ s, Klong.time s ∈ last.ks → s ≤ c.i)
    (hlastV : (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode).lastVersion c.i = last)
    (hlen2 : c.p.splitAbove < last.size → 2 ≤ (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode).live.length)
    (hrangeL : c.p.splitAbove < last.size → (Nn D).leaf = false →
      ∀ c' z, (c', z) ∈ (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode).live → 0 < c' →
      K (D + 1) ≤ c' ∧ ∀ c'' z', (c'', z') ∈ (Nn D).live → K (D + 1) < c'' → c' < c'')
    (hspaceL : (!compact && decide (last.size > c.p.splitAbove)) = true →
      (Nn D).leaf = false ∨ ((Nn (D + 1)).firstTime ≠ some c.i → ∀ i', s < i' → i' < D + 1 → ChainOrd c K Nn i'))
    (w : W) (hS1 : w.path = path0)
    (hS2 : ∀ i, s ≤ i → i ≤ D + 1 →
      w.nodes.lookup (X i) = some (Nn i) ∧ w.taken.contains (X i) = false)
    (hS3 : TreeOK (wNode c.p base w) c.i w.top.rootKey)
    (hS4 : ∀ i, s ≤ i → i ≤ D + 1 → TReach (wNode c.p base w) c.i w.top.rootKey (X i))
    (hS5 : ∀ z, w.next ≤ z → w.nodes.lookup z = none ∧ w.taken.contains z = false ∧
      knodeOf c.p base z = none)
    (hS6 : ∀ u c' z, TLink (wNode c.p base w) c.i u c' z → z < w.next)
    (hR0 : s = 0 → ¬ ChainRoom c (Nn 0) → w.top.rootKey = X 0)
    (hW : ∀ z zn, wNode c.p base w z = some zn → klongsWf zn.ks = true)
    (hV : TreeOK (updN (wNode c.p base w) (X (D + 1)) (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode)) c.i w.top.rootKey)
    (hvx : ∀ c' z, (c', z) ∈ (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode).liveAt c.i → z < w.next) :
    WriterWP (handleFullWith (fun q more => appendKlongs D q more) (D + 1) (X (D + 1)) [] last compact)
      c w (fun _ w' =>
      TreeOK (wNode c.p base w') c.i w'.top.rootKey ∧
      ((w'.top = w.top ∨ (s = 0 ∧ w.next ≤ w'.top.rootKey)) ∧ w'.taken = w.taken ∧ w'.path = w.path ∧
        w.next ≤ w'.next ∧ w'.vals = w.vals) ∧
      (∀ z, z < w.next → (∀ i, s ≤ i → i ≤ D + 1 → z ≠ X i) → w'.nodes.lookup z = w.nodes.lookup z) ∧
      (∀ z, TReach (wNode c.p base w') c.i w'.top.rootKey z →
        TReach (updN (wNode c.p base w) (X (D + 1)) (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode)) c.i w.top.rootKey z ∨ (w.next ≤ z ∧ z < w'.next)) ∧
      (∀ z zn, wNode c.p base w' z = some zn → klongsWf zn.ks = true) ∧
      (∀ Val : NodeId → Option Nat, (∀ z, (w.next ≤ z ∨ ∃ i, s ≤ i ∧ i ≤ D + 1 ∧ z = X i) → Val z = none) →
        (SegFits (wNode c.p base w') c.i (fuelR - 1) w'.top.rootKey ∨
          (ChainNoNewRoot c Nn s D ∧ LevelNoRoot c Nn D last compact)) →
        ∀ key, getFromR (wNode c.p base w') Val c.i fuelR key w'.top.rootKey =
          getFromR (updN (wNode c.p base w) (X (D + 1)) (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode)) Val c.i fuelR key w.top.rootKey) ∧
      (TReach (wNode c.p base w') c.i w'.top.rootKey (X (D + 1)) →
        ∀ n, wNode c.p base w' (X (D + 1)) = some n → ∀ cv y, Klong.key cv y ∈ n.ks → Klong.key cv y ∈ last.ks) ∧
      ((∀ i, s < i → i ≤ D → ChainOrd c K Nn i) → LastOrd c K Nn D last →
        ∀ z, TReach (updN (wNode c.p base w) (X (D + 1)) (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode)) c.i
          w.top.rootKey z → (∀ i, s ≤ i → i ≤ D + 1 → z ≠ X i) →
          TReach (wNode c.p base w') c.i w'.top.rootKey z) ∧
      ((∀ i, s < i → i ≤ D → ChainOrd c K Nn i) → LastOrd c K Nn D last →
        (∀ i, s ≤ i → i ≤ D + 1 → TReach (wNode c.p base w') c.i w'.top.rootKey (X i) ∨
          w'.nodes.lookup (X i) = some ((Nn i).toPrev (c.i - 1))) ∧
        (∀ z, w.next ≤ z → (w'.nodes.lookup z).isSome = true →
          TReach (wNode c.p base w') c.i w'.top.rootKey z))) := by
  have hchain := writerWP_appendKlongs_chainGRVf c base path0 s D X K Nn fuelR hfR
    (fun i h1 h2 => hX i h1 (by omega)) (fun i h1 h2 => hK i h1 (by omega))
    (fun i h1 h2 => hlinkK i h1 (by omega)) hrange hlen
    (fun i h1 h2 => hwf i h1 (by omega)) (fun i h1 h2 => htimes i h1 (by omega)) htop
    (fun i i' h1 h2 h3 h4 => hdist i i' h1 (by omega) h3 (by omega))
    hspace (D - s) (by omega)
  have hsD' : s + (D - s) = D := by omega
  rw [hsD'] at hchain
  have hj : s < D + 1 := by omega
  obtain ⟨hlk, htk⟩ := hS2 (D + 1) (by omega) (Nat.le_refl _)
  obtain ⟨hlq, htq⟩ := hS2 D hsD (by omega)
  have hpq : (w.path[D]?).map (·.2) = some (X D) := by
    rw [hS1]; exact hX D (by omega) (by omega)
  have hpk : w.path[D + 1]? = some (some (K (D + 1)), X (D + 1)) := by
    rw [hS1]; exact hK (D + 1) hj (Nat.le_refl _)
  have hkl : (K (D + 1), X (D + 1)) ∈ (Nn D).liveAt c.i := by
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
  have hqx : X D ≠ X (D + 1) := by
    intro h; have := hdist _ _ (by omega) (by omega) (by omega) (Nat.le_refl _) h; omega
  have hwq : wNode c.p base w (X D) = some (Nn D) := by
    simp only [wNode, htq, Bool.false_eq_true, ↓reduceIte, hlq]
  have hwx : wNode c.p base w (X (D + 1)) = some (Nn (D + 1)) := by
    simp only [wNode, htk, Bool.false_eq_true, ↓reduceIte, hlk]
  have hqR : TReach (updN (wNode c.p base w) (X (D + 1))
      ((⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode))) c.i w.top.rootKey
      (X D) :=
    tReach_updN_parent _ c.i _ _ _ _ _ hS3 (hS4 D (by omega) (by omega))
      ⟨Nn D, hwq, hkl⟩
  have hqtimes := htimes D (by omega) (by omega)
  have hqwf := hwf D (by omega) (by omega)
  have hxtimes := htimes (D + 1) (by omega) (Nat.le_refl _)
  have hxwf := hwf (D + 1) (by omega) (Nat.le_refl _)
  have hvxLinks : ∀ c' z, (c', z) ∈ ((⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode)).liveAt c.i → z < w.next := hvx
  have hVfresh : ∀ z, w.next ≤ z → ∀ u c', TReach (updN (wNode c.p base w) (X (D + 1))
      ((⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode))) c.i w.top.rootKey u →
      ¬ TLink (updN (wNode c.p base w) (X (D + 1))
        ((⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode))) c.i u c' z := by
    intro z hz u c' _ hl
    obtain ⟨m, hm, hc⟩ := hl
    by_cases hu : u = X (D + 1)
    · rw [hu, updN_self] at hm
      simp only [Option.some.injEq] at hm
      subst hm
      have := hvxLinks c' z hc; omega
    · rw [updN_ne _ _ _ _ hu] at hm
      exact hnoLink z hz u c' ⟨m, hm, hc⟩
  -- the facts of the reading at this level
  have hxv_wf : klongsWf ((⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode)).ks = true := hlwf
  have hxv_t : ∀ s, Klong.time s ∈ ((⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode)).ks → s ≤ c.i := hlt
  have hwfV : ∀ z zn, ReachS (updN (wNode c.p base w) (X (D + 1)) ((⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode))) c.i w.top.rootKey z → (updN (wNode c.p base w) (X (D + 1)) ((⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode))) z = some zn →
      klongsWf zn.ks = true := by
    intro z zn _ h
    by_cases hz : z = X (D + 1)
    · rw [hz, updN_self] at h; cases h; exact hxv_wf
    · rw [updN_ne _ _ _ _ hz] at h; exact hW z zn h
  have hrootN : ∀ z, w.next ≤ z → w.top.rootKey ≠ z := by
    intro z hz h
    obtain ⟨m, hm⟩ := hS3.rootKey
    have hwz : wNode c.p base w z = none := by
      obtain ⟨a, b, d⟩ := hS5 z hz
      simp only [wNode, b, Bool.false_eq_true, ↓reduceIte, a, d]
    rw [h, hwz] at hm; cases hm
  have hrootX : w.top.rootKey ≠ X (D + 1) := by
    intro h
    exact hV.rootFree (X D) (K (D + 1)) hqR
      ⟨Nn D, by rw [updN_ne _ _ _ _ hqx]; exact hwq, by rw [h]; exact hkl⟩
  have hVq : (updN (wNode c.p base w) (X (D + 1)) ((⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode))) (X D) = some (Nn D) := by rw [updN_ne _ _ _ _ hqx]; exact hwq
  have hrqV : ReachS (updN (wNode c.p base w) (X (D + 1)) ((⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode))) c.i w.top.rootKey (X D) := tReach_reachS _ _ _ _ hqR
  have hXn : ∀ z, w.next ≤ z → z ≠ X (D + 1) := by
    intro z hz h; have := hXlt (D + 1) (by omega) (Nat.le_refl _); omega
  have hQn : ∀ z, w.next ≤ z → z ≠ X D := by
    intro z hz h; have := hXlt D (by omega) (by omega); omega
  have hVfr : ∀ z, w.next ≤ z → (updN (wNode c.p base w) (X (D + 1)) ((⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode))) z = none := by
    intro z hz
    rw [updN_ne _ _ _ _ (hXn z hz)]
    obtain ⟨a, b, d⟩ := hS5 z hz
    simp only [wNode, b, Bool.false_eq_true, ↓reduceIte, a, d]
  have hVlt : ∀ u, TReach (updN (wNode c.p base w) (X (D + 1))
      ((⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode))) c.i w.top.rootKey u →
      u < w.next := by
    intro u hu
    rcases Nat.lt_or_ge u w.next with h | h
    · exact h
    · exact absurd hu (not_reach_fresh _ c.i _ u hV (hVfr u h) (fun u' c' hu' => hVfresh u h u' c' hu'))
  have hvalx : ∀ Val : NodeId → Option Nat,
      (∀ z, (w.next ≤ z ∨ ∃ i, s ≤ i ∧ i ≤ D + 1 ∧ z = X i) → Val z = none) →
      ∀ z, w.next ≤ z → Val (X (D + 1)) = Val z := by
    intro Val hVal z hz
    rw [hVal _ (Or.inr ⟨D + 1, by omega, Nat.le_refl _, rfl⟩), hVal _ (Or.inl hz)]
  -- the rest of a split: the parent's step by the induction, then the node left behind
  have hfinish : ∀ (w1 : W) (ins' : List (Nat × NodeId)) (N1 : NodeId → Option KNode)
      (New : NodeId → Prop),
      InsOK (Nn D) ins' → (∀ q ∈ ins', q.2 < w1.next) →
      w1.path = w.path → w1.taken = w.taken → w1.top = w.top → w.next + 2 ≤ w1.next →
      w1.vals = w.vals → (∀ z, New z → w.next ≤ z ∧ z < w1.next) →
      (∀ z, z < w.next → w1.nodes.lookup z = w.nodes.lookup z) →
      wNode c.p base w1 = N1 →
      TreeOK N1 c.i w.top.rootKey →
      (∀ i, s ≤ i → i ≤ D → TReach N1 c.i w.top.rootKey (X i)) →
      (∀ z, w1.next ≤ z → w1.nodes.lookup z = none ∧ w1.taken.contains z = false ∧
        knodeOf c.p base z = none) →
      (∀ u c' z, TLink N1 c.i u c' z → z < w1.next) →
      TreeOK (updN N1 (X D) (ins'.foldl (fun n (cv, y) => n.add c.i (.key cv y))
        (Nn D))) c.i w.top.rootKey →
      (∀ z, TReach (updN N1 (X D) (ins'.foldl (fun n (cv, y) => n.add c.i (.key cv y))
        (Nn D))) c.i w.top.rootKey z →
        (TReach (updN (wNode c.p base w) (X (D + 1))
          ((⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode))) c.i
          w.top.rootKey z ∨ New z) ∧ z ≠ X (D + 1)) →
      (∀ z zn, N1 z = some zn → klongsWf zn.ks = true) →
      (∀ Val : NodeId → Option Nat,
        (∀ z, (w.next ≤ z ∨ ∃ i, s ≤ i ∧ i ≤ D + 1 ∧ z = X i) → Val z = none) →
        (((∀ i, s < i → i ≤ D → ChainOrd c K Nn i) → ∀ z,
            (∃ c', (c', z) ∈ (ins'.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn D)).liveAt c.i) →
            w.next ≤ z →
            SegDepthLe (updN N1 (X D) (ins'.foldl (fun n (cv, y) => n.add c.i (.key cv y))
              (Nn D))) c.i (fuelR - 1) z) ∨
          LevelNoRoot c Nn D last compact) →
        ∀ key, getFromR (updN N1 (X D) (ins'.foldl (fun n (cv, y) => n.add c.i (.key cv y))
        (Nn D))) Val c.i fuelR key w.top.rootKey =
        getFromR (updN (wNode c.p base w) (X (D + 1))
          ((⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode)))
          Val c.i fuelR key w.top.rootKey) →
      ((∀ i, s < i → i ≤ D → ChainOrd c K Nn i) → LastOrd c K Nn D last →
        ∀ z, TReach (updN (wNode c.p base w) (X (D + 1)) (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode)) c.i
          w.top.rootKey z → z ≠ X (D + 1) →
        TReach (updN N1 (X D) (ins'.foldl (fun n (cv, y) => n.add c.i (.key cv y))
          (Nn D))) c.i w.top.rootKey z) →
      ((∀ i, s < i → i ≤ D → ChainOrd c K Nn i) → LastOrd c K Nn D last →
        ∀ z, w.next ≤ z → z < w1.next → (w1.nodes.lookup z).isSome = true →
        TReach (updN N1 (X D) (ins'.foldl (fun n (cv, y) => n.add c.i (.key cv y))
          (Nn D))) c.i w.top.rootKey z) →
      WriterWP (appendKlongs D (X D) ins') c w1 (fun _ w2 =>
        WriterWP (do let m ← getNode (X (D + 1)); putNode (X (D + 1)) (m.toPrev (c.i - 1)))
          c w2 (fun _ w3 =>
          TreeOK (wNode c.p base w3) c.i w3.top.rootKey ∧
          ((w3.top = w.top ∨ (s = 0 ∧ w.next ≤ w3.top.rootKey)) ∧ w3.taken = w.taken ∧ w3.path = w.path ∧ w.next ≤ w3.next ∧ w3.vals = w.vals) ∧
          (∀ z, z < w.next → (∀ i, s ≤ i → i ≤ D + 1 → z ≠ X i) →
            w3.nodes.lookup z = w.nodes.lookup z) ∧
          (∀ z, TReach (wNode c.p base w3) c.i w3.top.rootKey z →
            TReach (updN (wNode c.p base w) (X (D + 1))
              ((⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode))) c.i
              w.top.rootKey z ∨ (w.next ≤ z ∧ z < w3.next)) ∧
          (∀ z zn, wNode c.p base w3 z = some zn → klongsWf zn.ks = true) ∧
          (∀ Val : NodeId → Option Nat, (∀ z, (w.next ≤ z ∨ ∃ i, s ≤ i ∧ i ≤ D + 1 ∧ z = X i) → Val z = none) →
            (SegFits (wNode c.p base w3) c.i (fuelR - 1) w3.top.rootKey ∨
              (ChainNoNewRoot c Nn s D ∧ LevelNoRoot c Nn D last compact)) →
            ∀ key, getFromR (wNode c.p base w3) Val c.i fuelR key w3.top.rootKey =
            getFromR (updN (wNode c.p base w) (X (D + 1))
              ((⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode))) Val c.i fuelR key
              w.top.rootKey) ∧
            (TReach (wNode c.p base w3) c.i w3.top.rootKey (X (D + 1)) →
              ∀ n, wNode c.p base w3 (X (D + 1)) = some n → ∀ cv y, Klong.key cv y ∈ n.ks →
                Klong.key cv y ∈ last.ks) ∧
          ((∀ i, s < i → i ≤ D → ChainOrd c K Nn i) → LastOrd c K Nn D last →
            ∀ z, TReach (updN (wNode c.p base w) (X (D + 1)) (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode)) c.i
              w.top.rootKey z → (∀ i, s ≤ i → i ≤ D + 1 → z ≠ X i) →
              TReach (wNode c.p base w3) c.i w3.top.rootKey z) ∧
          ((∀ i, s < i → i ≤ D → ChainOrd c K Nn i) → LastOrd c K Nn D last →
            (∀ i, s ≤ i → i ≤ D + 1 → TReach (wNode c.p base w3) c.i w3.top.rootKey (X i) ∨
              w3.nodes.lookup (X i) = some ((Nn i).toPrev (c.i - 1))) ∧
            (∀ z, w.next ≤ z → (w3.nodes.lookup z).isSome = true →
              TReach (wNode c.p base w3) c.i w3.top.rootKey z)))) := by
    intro w1 ins' N1 New hins' hinsT' h1path h1t h1top h1next h1vals hNew h1low hN1 hT1 hR1 hS5' hS6' hV1 hRV1 hW1 hlev hRBs hNewR
    have hpar := hchain w1 ins' hins' hinsT' (by rw [h1path, hS1])
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
    rintro _ w2 ⟨hT2, ⟨h2top, h2t, h2path, h2next, h2vals⟩, h2frame, h2reach, h2W, h2R, _, h2RB,
      h2RN⟩
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
    refine ⟨?_, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    rotate_left 10
    · intro h
      exfalso
      have h3top : w3.top = w2.top := by rw [← hw3]
      rw [hN3] at h
      try rw [h3top] at h
      exact hxR2 (tReach_updN_unreach _ c.i _ _ _ hxR2 _ h)
    · intro hHS hLO z hz hzX
      have hz1 := hRBs hHS hLO z hz (hzX _ (by omega) (Nat.le_refl _))
      have hz2 := h2RB hHS z (by rw [hN1, h1top]; exact hz1)
        (fun i h1 h2 => hzX i h1 (by omega))
      have h3top : w3.top = w2.top := by rw [← hw3]
      rw [hN3]
      try rw [h3top]
      exact tReach_updN_keep _ c.i _ _ _ hxR2 z hz2
    · intro hHS hLO
      obtain ⟨hR2c, hR3c⟩ := h2RN hHS
      have h3top : w3.top = w2.top := by rw [← hw3]
      refine ⟨fun i h1 h2 => ?_, fun z hz h => ?_⟩
      · rcases Nat.lt_or_ge i (D + 1) with hlt | hge
        · have hiX : ¬ X i = X (D + 1) := fun he => by
            have := hdist _ _ h1 (by omega) (by omega) (Nat.le_refl _) he; omega
          rcases hR2c i h1 (by omega) with h' | h'
          · left
            rw [hN3]
            try rw [h3top]
            exact tReach_updN_keep _ c.i _ _ _ hxR2 _ h'
          · right
            try rw [h3n]
            rw [lookup_upsert, ite_eq_right_of_eq_false _ _ (eq_false hiX)]
            exact h'
        · right
          have : i = D + 1 := by omega
          subst this
          try rw [h3n]
          rw [lookup_upsert, ite_eq_left_of_eq_true _ _ (eq_true rfl)]
      · have hzX : ¬ z = X (D + 1) := by
          have := hXlt (D + 1) (by omega) (Nat.le_refl _); omega
        have h2' : (w2.nodes.lookup z).isSome = true := by
          try rw [h3n] at h
          rw [lookup_upsert, ite_eq_right_of_eq_false _ _ (eq_false hzX)] at h; exact h
        rw [hN3]
        try rw [h3top]
        apply tReach_updN_keep _ c.i _ _ _ hxR2
        rcases Nat.lt_or_ge z w1.next with hlt | hge
        · have h1' : (w1.nodes.lookup z).isSome = true := by
            rw [← h2frame z hlt (fun i h1 h2 he => by have := hXlt i h1 (by omega); omega)]
            exact h2'
          have hzV := hNewR hHS hLO z hz hlt h1'
          exact h2RB hHS z (by rw [hN1, h1top]; exact hzV)
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
      by_cases hz : z = X (D + 1)
      · rw [hz, updN_self] at h
        cases h
        exact KNode.toPrev_wf _ _ (hwf (D + 1) (by omega) (Nat.le_refl _))
      · rw [updN_ne _ _ _ _ hz] at h
        exact h2W z zn h
    · intro Val hVal hfit key
      have h3top : w3.top = w2.top := by rw [← hw3]
      have hfit2 : SegFits (wNode c.p base w2) c.i (fuelR - 1) w2.top.rootKey ∨
          ChainNoNewRoot c Nn s D := by
        rcases hfit with hf | hf
        · left
          rw [hN3] at hf
          try rw [h3top] at hf
          exact SegFits.of_agree _ _ c.i _ _
            (fun x hx => updN_ne _ _ _ _ (fun he : x = X (D + 1) => hxR2 (he ▸ hx))) hf
        · exact Or.inr hf.1
      rw [hN3]
      try rw [h3top]
      rw [getFromR_updN_unreach' (wNode c.p base w2) Val c.i fuelR w2.top.rootKey
        (X (D + 1)) _ (fun z zn _ h => h2W z zn h)
        (fun h => hxR2 (reachS_tReach _ _ _ _ h)) key]
      rw [h2R Val (fun z hz => hVal z (by
        rcases hz with h | ⟨i, h1, h2, h3⟩
        · exact Or.inl (by omega)
        · exact Or.inr ⟨i, h1, by omega, h3⟩)) hfit2 key, h1top, hN1]
      refine hlev Val hVal ?_ key
      rcases hfit with hf | hf
      · left
        intro hHS z ⟨c', hc'⟩ hzn
        have hf2 : SegFits (wNode c.p base w2) c.i (fuelR - 1) w2.top.rootKey := by
          rw [hN3] at hf
          try rw [h3top] at hf
          exact SegFits.of_agree _ _ c.i _ _
            (fun x hx => updN_ne _ _ _ _ (fun he : x = X (D + 1) => hxR2 (he ▸ hx))) hf
        have hqR' : TReach (updN N1 (X D) (ins'.foldl (fun n (cv, y) => n.add c.i (.key cv y))
            (Nn D))) c.i w.top.rootKey (X D) :=
          tReach_updN_self _ c.i _ _ _ hT1 (hR1 D (by omega) (Nat.le_refl _))
        have hzR := TReach.link hqR' ⟨_, updN_self _ _ _, hc'⟩
        have hz2 := h2RB hHS z (by rw [hN1, h1top]; exact hzR)
          (fun i h1 h2 he => by have := hXlt i h1 (by omega); omega)
        have hd2 := hf2 z (tReach_reachS _ _ _ _ hz2)
        refine SegDepthLe.of_agree _ _ c.i _ z ?_ hd2
        intro y hy
        have hyR : ReachS (updN N1 (X D) (ins'.foldl (fun n (cv, y) => n.add c.i (.key cv y))
            (Nn D))) c.i w.top.rootKey y :=
          reachS_trans _ c.i _ z (tReach_reachS _ _ _ _ hzR) y hy
        have hylt : y < w1.next := by
          cases hyR with
          | root =>
            have := Nat.lt_of_not_le (fun h => hrootN _ h rfl)
            omega
          | step u un c'' _ hu hun hmem =>
            by_cases hux : u = X D
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
        have hyX : ∀ i, s ≤ i → i ≤ D → y ≠ X i := by
          intro i h1 h2 he
          have hXi : ReachS (updN N1 (X D) (ins'.foldl (fun n (cv, y) => n.add c.i (.key cv y))
              (Nn D))) c.i (X i) z := by
            refine reachS_trans _ c.i _ (X D) ?_ z (ReachS.step _ _ c' z ReachS.root (updN_self _ _ _) hc')
            refine chain_reachS _ c.i X K Nn i D h2 ?_
            intro i' h1' h2'
            have hne : X i' ≠ X D := fun hh => by
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
        rw [updN_ne _ _ _ _ (hyX D (by omega) (Nat.le_refl _)), ← hN1]
        simp only [wNode, h2t, h2frame y hylt hyX]
      · right
        exact hf.2
  have hanc : ∀ m : KNode, ∀ i, s ≤ i → i ≤ D →
      TReach (updN (wNode c.p base w) (X (D + 1)) m) c.i w.top.rootKey (X i) :=
    fun m i h1 h2 => chain_anc_reach (wNode c.p base w) c.i w.top.rootKey X s (D + 1) hS3
      (hS4 s (Nat.le_refl _) (by omega))
      (fun i' h1' h2' => by
        obtain ⟨a, b⟩ := hS2 (i' - 1) (by omega) (by omega)
        exact ⟨K i', Nn (i' - 1), by simp only [wNode, b, Bool.false_eq_true, ↓reduceIte, a],
          hlinkK i' h1' (by omega)⟩) m i h1 (by omega)
  have hstepT : (Nn (D + 1)).firstTime ≠ some c.i →
      (!compact && decide (last.size > c.p.splitAbove)) = false →
      WriterWP (handleFullWith (fun q more => appendKlongs D q more) (D + 1)
        (X (D + 1)) [] last compact) c w (fun _ w' =>
        TreeOK (wNode c.p base w') c.i w'.top.rootKey ∧
          ((w'.top = w.top ∨ (s = 0 ∧ w.next ≤ w'.top.rootKey)) ∧ w'.taken = w.taken ∧ w'.path = w.path ∧
            w.next ≤ w'.next ∧ w'.vals = w.vals) ∧
          (∀ z, z < w.next → (∀ i, s ≤ i → i ≤ D + 1 → z ≠ X i) → w'.nodes.lookup z = w.nodes.lookup z) ∧
          (∀ z, TReach (wNode c.p base w') c.i w'.top.rootKey z →
            TReach (updN (wNode c.p base w) (X (D + 1)) (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode)) c.i w.top.rootKey z ∨ (w.next ≤ z ∧ z < w'.next)) ∧
          (∀ z zn, wNode c.p base w' z = some zn → klongsWf zn.ks = true) ∧
          (∀ Val : NodeId → Option Nat, (∀ z, (w.next ≤ z ∨ ∃ i, s ≤ i ∧ i ≤ D + 1 ∧ z = X i) → Val z = none) →
            (SegFits (wNode c.p base w') c.i (fuelR - 1) w'.top.rootKey ∨
              (ChainNoNewRoot c Nn s D ∧ LevelNoRoot c Nn D last compact)) →
            ∀ key, getFromR (wNode c.p base w') Val c.i fuelR key w'.top.rootKey =
              getFromR (updN (wNode c.p base w) (X (D + 1)) (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode)) Val c.i fuelR key w.top.rootKey) ∧
          (TReach (wNode c.p base w') c.i w'.top.rootKey (X (D + 1)) →
            ∀ n, wNode c.p base w' (X (D + 1)) = some n → ∀ cv y, Klong.key cv y ∈ n.ks →
              Klong.key cv y ∈ last.ks) ∧
          ((∀ i, s < i → i ≤ D → ChainOrd c K Nn i) → LastOrd c K Nn D last →
            ∀ z, TReach (updN (wNode c.p base w) (X (D + 1)) (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode)) c.i
              w.top.rootKey z → (∀ i, s ≤ i → i ≤ D + 1 → z ≠ X i) →
              TReach (wNode c.p base w') c.i w'.top.rootKey z) ∧
          ((∀ i, s < i → i ≤ D → ChainOrd c K Nn i) → LastOrd c K Nn D last →
            (∀ i, s ≤ i → i ≤ D + 1 → TReach (wNode c.p base w') c.i w'.top.rootKey (X i) ∨
              w'.nodes.lookup (X i) = some ((Nn i).toPrev (c.i - 1))) ∧
            (∀ z, w.next ≤ z → (w'.nodes.lookup z).isSome = true →
              TReach (wNode c.p base w') c.i w'.top.rootKey z))) := by
    intro hfirst hcs
    apply writerWP_handleFullWith_time_up_last' D (X (D + 1)) (X D) (Nn (D + 1))
      (Nn D) (K (D + 1)) last compact c w hlk hlq hfirst hcs hpq hpk
    intro w1 h1n h1t h1top h1path h1next h1vals
    have hN1 : wNode c.p base w1 = updN (wNode c.p base w) w.next ⟨(Nn (D + 1)).leaf, last.ks⟩ :=
      wNode_append_updN c.p base w w1 _ h1n h1t hfree0 htk0
    have hlsub : ∀ c' z, (c', z) ∈ (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode).liveAt c.i →
        (c', z) ∈ ((⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode)).liveAt c.i := fun _ _ h => h
    obtain ⟨hT1V, hR1V⟩ := treeOK_timeSplit_gen (updN (wNode c.p base w) (X (D + 1))
        ((⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode)))
      (updN (wNode c.p base w1) (X D) ([(K (D + 1), w.next)].foldl
        (fun n (cv, y) => n.add c.i (.key cv y)) (Nn D))) c.i w.top.rootKey (X D)
      (X (D + 1)) w.next (Nn D)
      ((⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode))
      ⟨(Nn (D + 1)).leaf, last.ks⟩
      ([(K (D + 1), w.next)].foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn D))
      (K (D + 1)) hV hqR (by rw [updN_ne _ _ _ _ hqx]; exact hwq)
      hkl (updN_self _ _ _) (updN_self _ _ _)
      (fun c' z h => KNode.add_key_liveAt_mem _ c.i _ _ hqwf hqtimes c' z h)
      (by
        rw [updN_ne _ _ _ _ (fun h => by have := hXlt D (by omega) (by omega); omega), hN1]
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
      (by
        intro z zn h
        by_cases hz : z = w.next
        · rw [hz, updN_self] at h; cases h; exact hlwf
        · rw [updN_ne _ _ _ _ hz] at h; exact hW z zn h)
      (by
        intro Val hVal _
        cases hqlf : (Nn D).leaf with
        | false =>
          exact getFromR_timeLevel _ _ Val c.i fuelR w.top.rootKey (X D)
            (X (D + 1)) w.next (Nn D) _ ⟨(Nn (D + 1)).leaf, last.ks⟩
            (K (D + 1)) hV hwfV hVq hrqV hqlf hqwf hqtimes hkl hqx (updN_self _ _ _) hxv_wf
            hxv_t (hVfr w.next (Nat.le_refl _))
            (fun u c' hu => hVfresh w.next (Nat.le_refl _) u c' (reachS_tReach _ _ _ _ hu))
            (by rw [updN_ne _ _ _ _ (hQn w.next (Nat.le_refl _)), updN_self])
            rfl hlwf hlt
            (fun c' => rfl)
            (updN_self _ _ _)
            (by intro z h1 h2 h3; rw [updN_ne _ _ _ _ h2, updN_ne _ _ _ _ h3, updN_ne _ _ _ _ h1])
            (hvalx Val hVal w.next (Nat.le_refl _)) (hrootN w.next (Nat.le_refl _)) hrootX
        | true =>
          exact getFromR_segTimeLevel _ _ Val c.i fuelR w.top.rootKey (X D)
            (X (D + 1)) w.next (Nn D) _ ⟨(Nn (D + 1)).leaf, last.ks⟩
            (K (D + 1)) hV hwfV hVq hrqV hqlf hqwf hqtimes hkl hqx (updN_self _ _ _) hxv_wf
            hxv_t (hVfr w.next (Nat.le_refl _))
            (fun u c' hu => hVfresh w.next (Nat.le_refl _) u c' (reachS_tReach _ _ _ _ hu))
            (by rw [updN_ne _ _ _ _ (hQn w.next (Nat.le_refl _)), updN_self])
            rfl hlwf hlt
            (fun c' => rfl)
            (updN_self _ _ _)
            (by intro z h1 h2 h3; rw [updN_ne _ _ _ _ h2, updN_ne _ _ _ _ h3, updN_ne _ _ _ _ h1])
            (hvalx Val hVal w.next (Nat.le_refl _)) (hrootN w.next (Nat.le_refl _)) hrootX)
      (by
        intro _ _ z hz hzx
        have hTN1 : TreeOK (updN (wNode c.p base w) w.next ⟨(Nn (D + 1)).leaf, last.ks⟩) c.i
            w.top.rootKey :=
          treeOK_updN_unreach _ c.i _ _ _ hS3 (hyR w.next (Nat.le_refl _))
        have hRq : TReach (updN (wNode c.p base w) w.next ⟨(Nn (D + 1)).leaf, last.ks⟩) c.i
            w.top.rootKey (X D) := by
          obtain ⟨a, ha⟩ := (hS4 D (by omega) (by omega)).pathLen
          exact tReach_updN_of_short _ c.i _ _ _ a _ ha
            (fun b hb => absurd hb.reach (hyR w.next (Nat.le_refl _)))
        have hRq' := tReach_updN_self _ c.i _ _ ([(K (D + 1), w.next)].foldl
          (fun n (cv, y) => n.add c.i (.key cv y)) (Nn D)) hTN1 hRq
        have hy : TReach (updN (updN (wNode c.p base w) w.next ⟨(Nn (D + 1)).leaf, last.ks⟩)
            (X D) ([(K (D + 1), w.next)].foldl (fun n (cv, y) => n.add c.i (.key cv y))
              (Nn D))) c.i w.top.rootKey w.next :=
          TReach.link hRq' ⟨_, updN_self _ _ _, KNode.add_key_liveAt_self _ c.i _ _ hqwf hqtimes⟩
        refine tReach_transport _ _ c.i w.top.rootKey w.top.rootKey (X (D + 1)) _ (updN_self _ _ _)
          ?_ ?_ ?_ z hz hzx
        · exact (fun _ => TReach.root)
        · exact (fun u c' z' hu hux _ hl hzx' => by
            obtain ⟨mm, hm, hc⟩ := hl
            by_cases huq : u = X D
            · subst huq
              rw [updN_ne _ _ _ _ hqx, hwq] at hm
              cases hm
              exact ⟨_, updN_self _ _ _, insOK_keep c.i _ _ (Or.inl ⟨_, _, rfl⟩) (K (D + 1))
                (fun a ha => by simp at ha; rw [← ha]) hqwf hqtimes _ hkl c' z' hc hzx'⟩
            · have hun : u ≠ w.next := by have := hVlt u hu; omega
              rw [updN_ne _ _ _ _ hux] at hm
              exact ⟨mm, by rw [updN_ne _ _ _ _ huq, updN_ne _ _ _ _ hun]; exact hm, hc⟩)
        · exact (fun c' z' hc => TReach.link hy ⟨⟨(Nn (D + 1)).leaf, last.ks⟩, by
              rw [updN_ne _ _ _ _ (fun h => by have := hXlt D (by omega) (by omega); omega)]
              exact updN_self _ _ _, hc⟩))
      (by
        intro _ _ z hz hlt h
        have hzn : z = w.next := by
          refine Classical.byContradiction (fun hne => ?_)
          rw [h1n, List.lookup_append, (hS5 z hz).1] at h
          have hb : (z == w.next) = false := by simp only [beq_eq_false_iff_ne, ne_eq]; exact hne
          simp [List.lookup, hb] at h
        subst hzn
        have hTN1 : TreeOK (updN (wNode c.p base w) w.next ⟨(Nn (D + 1)).leaf, last.ks⟩) c.i
            w.top.rootKey :=
          treeOK_updN_unreach _ c.i _ _ _ hS3 (hyR w.next (Nat.le_refl _))
        have hRq : TReach (updN (wNode c.p base w) w.next ⟨(Nn (D + 1)).leaf, last.ks⟩) c.i
            w.top.rootKey (X D) := by
          obtain ⟨a, ha⟩ := (hS4 D (by omega) (by omega)).pathLen
          exact tReach_updN_of_short _ c.i _ _ _ a _ ha
            (fun b hb => absurd hb.reach (hyR w.next (Nat.le_refl _)))
        have hRq' := tReach_updN_self _ c.i _ _ ([(K (D + 1), w.next)].foldl
          (fun n (cv, y) => n.add c.i (.key cv y)) (Nn D)) hTN1 hRq
        exact TReach.link hRq' ⟨_, updN_self _ _ _, KNode.add_key_liveAt_self _ c.i _ _ hqwf hqtimes⟩)

  have hstepS : (Nn (D + 1)).firstTime ≠ some c.i → (Nn D).leaf = false →
      c.p.splitAbove < last.size →
      WriterWP (handleFullWith (fun q more => appendKlongs D q more) (D + 1)
        (X (D + 1)) [] last false) c w (fun _ w' =>
        TreeOK (wNode c.p base w') c.i w'.top.rootKey ∧
          ((w'.top = w.top ∨ (s = 0 ∧ w.next ≤ w'.top.rootKey)) ∧ w'.taken = w.taken ∧ w'.path = w.path ∧
            w.next ≤ w'.next ∧ w'.vals = w.vals) ∧
          (∀ z, z < w.next → (∀ i, s ≤ i → i ≤ D + 1 → z ≠ X i) → w'.nodes.lookup z = w.nodes.lookup z) ∧
          (∀ z, TReach (wNode c.p base w') c.i w'.top.rootKey z →
            TReach (updN (wNode c.p base w) (X (D + 1)) (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode)) c.i w.top.rootKey z ∨ (w.next ≤ z ∧ z < w'.next)) ∧
          (∀ z zn, wNode c.p base w' z = some zn → klongsWf zn.ks = true) ∧
          (∀ Val : NodeId → Option Nat, (∀ z, (w.next ≤ z ∨ ∃ i, s ≤ i ∧ i ≤ D + 1 ∧ z = X i) → Val z = none) →
            (SegFits (wNode c.p base w') c.i (fuelR - 1) w'.top.rootKey ∨
              (ChainNoNewRoot c Nn s D ∧ LevelNoRoot c Nn D last compact)) →
            ∀ key, getFromR (wNode c.p base w') Val c.i fuelR key w'.top.rootKey =
              getFromR (updN (wNode c.p base w) (X (D + 1)) (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode)) Val c.i fuelR key w.top.rootKey) ∧
          (TReach (wNode c.p base w') c.i w'.top.rootKey (X (D + 1)) →
            ∀ n, wNode c.p base w' (X (D + 1)) = some n → ∀ cv y, Klong.key cv y ∈ n.ks →
              Klong.key cv y ∈ last.ks) ∧
          ((∀ i, s < i → i ≤ D → ChainOrd c K Nn i) → LastOrd c K Nn D last →
            ∀ z, TReach (updN (wNode c.p base w) (X (D + 1)) (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode)) c.i
              w.top.rootKey z → (∀ i, s ≤ i → i ≤ D + 1 → z ≠ X i) →
              TReach (wNode c.p base w') c.i w'.top.rootKey z) ∧
          ((∀ i, s < i → i ≤ D → ChainOrd c K Nn i) → LastOrd c K Nn D last →
            (∀ i, s ≤ i → i ≤ D + 1 → TReach (wNode c.p base w') c.i w'.top.rootKey (X i) ∨
              w'.nodes.lookup (X i) = some ((Nn i).toPrev (c.i - 1))) ∧
            (∀ z, w.next ≤ z → (w'.nodes.lookup z).isSome = true →
              TReach (wNode c.p base w') c.i w'.top.rootKey z))) := by
    intro hfirst hql hsp
    have h2l := hlen2 hsp
    obtain ⟨r, hdiv0, hsc, hrm, hfh0, hsh0⟩ := halves_facts_nil c.i (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode) h2l hlt
    have hhalf0 := halves_read_nil c.i (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode) h2l hlt hlwf
    have hwh0 := halves_newKlongs_wf (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode).leaf c.i (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode).live []
    rw [← KNode.lastVersion_eq_newKlongs] at hwh0
    rw [hlastV] at hdiv0 hfh0 hsh0 hhalf0 hwh0
    have hdiv : (halves (Nn (D + 1)).leaf c.i last []).2.2 = r.1 := hdiv0
    have hfh : ∀ c' z, (c', z) ∈ (halves (Nn (D + 1)).leaf c.i last []).1.liveAt c.i → c' < r.1 ∧
        (c', z) ∈ (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode).liveAt c.i := hfh0
    have hsh : ∀ c' z, (c', z) ∈ (halves (Nn (D + 1)).leaf c.i last []).2.1.liveAt c.i →
        ∃ c0, r.1 ≤ c0 ∧ c' = splitLocalCv (Nn (D + 1)).leaf r.1 c0 ∧ (c0, z) ∈ (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode).liveAt c.i := hsh0
    have hhalf : (halves (Nn (D + 1)).leaf c.i last []).1.leaf = (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode).leaf ∧
        (halves (Nn (D + 1)).leaf c.i last []).2.1.leaf = (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode).leaf ∧
        ((⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode).leaf = true → ∀ c' : Nat, c' < (halves (Nn (D + 1)).leaf c.i last []).2.2 →
          ((halves (Nn (D + 1)).leaf c.i last []).1.searchEq c.i c').map (·.y) =
            ((⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode).searchEq c.i c').map (·.y)) ∧
        ((⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode).leaf = true → ∀ c' : Nat, (halves (Nn (D + 1)).leaf c.i last []).2.2 ≤ c' →
          ((halves (Nn (D + 1)).leaf c.i last []).2.1.searchEq c.i c').map (·.y) =
            ((⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode).searchEq c.i c').map (·.y)) ∧
        ((⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode).leaf = false → ∀ c' : Nat, c' < (halves (Nn (D + 1)).leaf c.i last []).2.2 →
          ((halves (Nn (D + 1)).leaf c.i last []).1.searchLte c.i c').map (·.y) =
            ((⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode).searchLte c.i c').map (·.y)) ∧
        ((⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode).leaf = false → ∀ c' : Nat, (halves (Nn (D + 1)).leaf c.i last []).2.2 ≤ c' →
          ((halves (Nn (D + 1)).leaf c.i last []).2.1.searchLte c.i c').map (·.y) =
            ((⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode).searchLte c.i c').map (·.y)) := hhalf0
    have hwh : klongsWf (halves (Nn (D + 1)).leaf c.i last []).1.ks = true ∧
        klongsWf (halves (Nn (D + 1)).leaf c.i last []).2.1.ks = true := hwh0
    have hcov0 := halves_cover_nil c.i (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode) h2l hlt hlwf
    rw [hlastV] at hcov0
    have hcov : ∀ c' z, (c', z) ∈ (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode).liveAt c.i →
        (c' < (halves (Nn (D + 1)).leaf c.i last []).2.2 →
          ∃ c'', (c'', z) ∈ (halves (Nn (D + 1)).leaf c.i last []).1.liveAt c.i) ∧
        ((halves (Nn (D + 1)).leaf c.i last []).2.2 ≤ c' →
          ∃ c'', (c'', z) ∈ (halves (Nn (D + 1)).leaf c.i last []).2.1.liveAt c.i) := hcov0
    apply writerWP_handleFullWith_space_up_last D (X (D + 1)) (X D) (Nn (D + 1))
      (Nn D) (K (D + 1)) last c w hlk hlq hql hfirst hsp hpq hpk
    intro w1 h1n h1t h1top h1path h1next h1vals
    obtain ⟨out, hout⟩ : ∃ o, halves (Nn (D + 1)).leaf c.i last [] = o :=
      ⟨_, rfl⟩
    rw [hout] at h1n hdiv hfh hsh hhalf hwh hcov ⊢
    rw [hdiv] at hhalf hcov
    rw [hdiv]
    have h12 : w.next ≠ w.next + 2 := by omega
    have hN1 : wNode c.p base w1 = updN (updN (wNode c.p base w) w.next out.1) (w.next + 2) out.2.1 :=
      wNode_two_updN c.p base w w1 _ _ _ _ h1n h1t h12 htk0 htk2'
    have hf := hfh
    have hs := hsh
    have hq1wf := KNode.add_key_wf (Nn D) c.i (K (D + 1)) w.next hqwf
    have hq1t := KNode.add_times (Nn D) c.i (.key (K (D + 1)) w.next)
      (fun s h => by cases h) hqtimes
    have hqlinks : ∀ c' z, (c', z) ∈ ([(K (D + 1), w.next), (r.1, w.next + 2)].foldl
        (fun n (cv, y) => n.add c.i (.key cv y)) (Nn D)).liveAt c.i →
        (c' = r.1 ∧ z = w.next + 2) ∨ (c' ≠ r.1 ∧ c' = K (D + 1) ∧ z = w.next) ∨
        (c' ≠ r.1 ∧ c' ≠ K (D + 1) ∧ (c', z) ∈ (Nn D).liveAt c.i) := by
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
    have hQn1 : X D ≠ w.next := by have := hXlt D (by omega) (by omega); omega
    have hQn2 : X D ≠ w.next + 2 := by have := hXlt D (by omega) (by omega); omega
    obtain ⟨hT1V, hR1V⟩ := treeOK_spaceSplit_gen (updN (wNode c.p base w) (X (D + 1))
        ((⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode)))
      (updN (wNode c.p base w1) (X D) ([(K (D + 1), w.next), (r.1, w.next + 2)].foldl
        (fun n (cv, y) => n.add c.i (.key cv y)) (Nn D))) c.i w.top.rootKey (X D)
      (X (D + 1)) w.next (w.next + 2) (Nn D)
      ((⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode)) out.1 out.2.1
      ([(K (D + 1), w.next), (r.1, w.next + 2)].foldl
        (fun n (cv, y) => n.add c.i (.key cv y)) (Nn D))
      (K (D + 1)) r.1 (splitLocalCv (Nn (D + 1)).leaf r.1) hV hqR
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
    have hrK := hrangeL hsp hql r.1 r.2 hrm hsc
    apply hfinish w1 [(K (D + 1), w.next), (r.1, w.next + 2)] _
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
        exact getFromR_spaceLevel _ _ Val c.i fuelR w.top.rootKey (X D) (X (D + 1))
          w.next (w.next + 2) (Nn D) _ out.1 out.2.1 (K (D + 1)) r.1 hV hwfV hVq hrqV
          hql hqwf hqtimes hkl hqx hrK.1
          (fun c' z hcz => by
            by_cases hle : c' ≤ K (D + 1)
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
        intro _ hLO z hz hzx
        have hKr := lastOrd_div c K Nn D last hLO hql hsp hlastV h2l
        rw [hout, hdiv] at hKr
        have hR2 : ¬ TReach (updN (wNode c.p base w) w.next out.1) c.i w.top.rootKey (w.next + 2) :=
          fun h => hyR (w.next + 2) (by omega)
            (tReach_updN_unreach _ c.i _ _ _ (hyR w.next (Nat.le_refl _)) _ h)
        have hTN1 : TreeOK (updN (updN (wNode c.p base w) w.next out.1) (w.next + 2) out.2.1) c.i
            w.top.rootKey :=
          treeOK_updN_unreach _ c.i _ _ _
            (treeOK_updN_unreach _ c.i _ _ _ hS3 (hyR w.next (Nat.le_refl _))) hR2
        have hRq : TReach (updN (updN (wNode c.p base w) w.next out.1) (w.next + 2) out.2.1) c.i
            w.top.rootKey (X D) := by
          obtain ⟨a, ha⟩ := (hS4 D (by omega) (by omega)).pathLen
          have h1r := tReach_updN_of_short _ c.i _ _ out.1 a _ ha
            (fun b hb => absurd hb.reach (hyR w.next (Nat.le_refl _)))
          obtain ⟨a', ha'⟩ := h1r.pathLen
          exact tReach_updN_of_short _ c.i _ _ _ a' _ ha' (fun b hb => absurd hb.reach hR2)
        have hRq' := tReach_updN_self _ c.i _ _ ([(K (D + 1), w.next), (r.1, w.next + 2)].foldl
          (fun n (cv, y) => n.add c.i (.key cv y)) (Nn D)) hTN1 hRq
        have hmemF : (K (D + 1), w.next) ∈ ([(K (D + 1), w.next), (r.1, w.next + 2)].foldl
            (fun n (cv, y) => n.add c.i (.key cv y)) (Nn D)).liveAt c.i := by
          apply KNode.addKeys_liveAt_of_fold c.i _ _ hqwf hqtimes
          have hne : (r.1 == K (D + 1)) = false := by
            simp only [beq_eq_false_iff_ne, ne_eq]; omega
          simp [pairLookupStep, hne]
        have hmemS : (r.1, w.next + 2) ∈ ([(K (D + 1), w.next), (r.1, w.next + 2)].foldl
            (fun n (cv, y) => n.add c.i (.key cv y)) (Nn D)).liveAt c.i := by
          apply KNode.addKeys_liveAt_of_fold c.i _ _ hqwf hqtimes
          simp [pairLookupStep]
        have hF := TReach.link hRq' ⟨_, updN_self _ _ _, hmemF⟩
        have hS := TReach.link hRq' ⟨_, updN_self _ _ _, hmemS⟩
        refine tReach_transport _ _ c.i w.top.rootKey w.top.rootKey (X (D + 1)) _ (updN_self _ _ _)
          ?_ ?_ ?_ z hz hzx
        · exact (fun _ => TReach.root)
        · exact (fun u c' z' hu hux _ hl hzx' => by
            obtain ⟨mm, hm, hc⟩ := hl
            by_cases huq : u = X D
            · subst huq
              rw [updN_ne _ _ _ _ hqx, hwq] at hm
              cases hm
              exact ⟨_, updN_self _ _ _, insOK_keep c.i _ _
                (Or.inr ⟨_, _, _, _, rfl, hrK.1, fun c'' z'' hm hlt => by
                  have := hrK.2 c'' z'' (by simpa using hm) hlt; exact this⟩)
                (K (D + 1)) (fun a ha => by simp at ha; rw [← ha]) hqwf hqtimes _ hkl c' z' hc
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
        intro _ hLO z hz hlt h
        have hKr := lastOrd_div c K Nn D last hLO hql hsp hlastV h2l
        rw [hout, hdiv] at hKr
        have hR2 : ¬ TReach (updN (wNode c.p base w) w.next out.1) c.i w.top.rootKey (w.next + 2) :=
          fun h => hyR (w.next + 2) (by omega)
            (tReach_updN_unreach _ c.i _ _ _ (hyR w.next (Nat.le_refl _)) _ h)
        have hTN1 : TreeOK (updN (updN (wNode c.p base w) w.next out.1) (w.next + 2) out.2.1) c.i
            w.top.rootKey :=
          treeOK_updN_unreach _ c.i _ _ _
            (treeOK_updN_unreach _ c.i _ _ _ hS3 (hyR w.next (Nat.le_refl _))) hR2
        have hRq : TReach (updN (updN (wNode c.p base w) w.next out.1) (w.next + 2) out.2.1) c.i
            w.top.rootKey (X D) := by
          obtain ⟨a, ha⟩ := (hS4 D (by omega) (by omega)).pathLen
          have h1r := tReach_updN_of_short _ c.i _ _ out.1 a _ ha
            (fun b hb => absurd hb.reach (hyR w.next (Nat.le_refl _)))
          obtain ⟨a', ha'⟩ := h1r.pathLen
          exact tReach_updN_of_short _ c.i _ _ _ a' _ ha' (fun b hb => absurd hb.reach hR2)
        have hRq' := tReach_updN_self _ c.i _ _ ([(K (D + 1), w.next), (r.1, w.next + 2)].foldl
          (fun n (cv, y) => n.add c.i (.key cv y)) (Nn D)) hTN1 hRq
        have hmemF : (K (D + 1), w.next) ∈ ([(K (D + 1), w.next), (r.1, w.next + 2)].foldl
            (fun n (cv, y) => n.add c.i (.key cv y)) (Nn D)).liveAt c.i := by
          apply KNode.addKeys_liveAt_of_fold c.i _ _ hqwf hqtimes
          have hne : (r.1 == K (D + 1)) = false := by
            simp only [beq_eq_false_iff_ne, ne_eq]; omega
          simp [pairLookupStep, hne]
        have hmemS : (r.1, w.next + 2) ∈ ([(K (D + 1), w.next), (r.1, w.next + 2)].foldl
            (fun n (cv, y) => n.add c.i (.key cv y)) (Nn D)).liveAt c.i := by
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

  have hstepTI : (Nn (D + 1)).firstTime = some c.i →
      (!compact && decide (last.size > c.p.splitAbove)) = false →
      WriterWP (handleFullWith (fun q more => appendKlongs D q more) (D + 1)
        (X (D + 1)) [] last compact) c w (fun _ w' =>
        TreeOK (wNode c.p base w') c.i w'.top.rootKey ∧
          ((w'.top = w.top ∨ (s = 0 ∧ w.next ≤ w'.top.rootKey)) ∧ w'.taken = w.taken ∧ w'.path = w.path ∧
            w.next ≤ w'.next ∧ w'.vals = w.vals) ∧
          (∀ z, z < w.next → (∀ i, s ≤ i → i ≤ D + 1 → z ≠ X i) → w'.nodes.lookup z = w.nodes.lookup z) ∧
          (∀ z, TReach (wNode c.p base w') c.i w'.top.rootKey z →
            TReach (updN (wNode c.p base w) (X (D + 1)) (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode)) c.i w.top.rootKey z ∨ (w.next ≤ z ∧ z < w'.next)) ∧
          (∀ z zn, wNode c.p base w' z = some zn → klongsWf zn.ks = true) ∧
          (∀ Val : NodeId → Option Nat, (∀ z, (w.next ≤ z ∨ ∃ i, s ≤ i ∧ i ≤ D + 1 ∧ z = X i) → Val z = none) →
            (SegFits (wNode c.p base w') c.i (fuelR - 1) w'.top.rootKey ∨
              (ChainNoNewRoot c Nn s D ∧ LevelNoRoot c Nn D last compact)) →
            ∀ key, getFromR (wNode c.p base w') Val c.i fuelR key w'.top.rootKey =
              getFromR (updN (wNode c.p base w) (X (D + 1)) (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode)) Val c.i fuelR key w.top.rootKey) ∧
          (TReach (wNode c.p base w') c.i w'.top.rootKey (X (D + 1)) →
            ∀ n, wNode c.p base w' (X (D + 1)) = some n → ∀ cv y, Klong.key cv y ∈ n.ks →
              Klong.key cv y ∈ last.ks) ∧
          ((∀ i, s < i → i ≤ D → ChainOrd c K Nn i) → LastOrd c K Nn D last →
            ∀ z, TReach (updN (wNode c.p base w) (X (D + 1)) (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode)) c.i
              w.top.rootKey z → (∀ i, s ≤ i → i ≤ D + 1 → z ≠ X i) →
              TReach (wNode c.p base w') c.i w'.top.rootKey z) ∧
          ((∀ i, s < i → i ≤ D → ChainOrd c K Nn i) → LastOrd c K Nn D last →
            (∀ i, s ≤ i → i ≤ D + 1 → TReach (wNode c.p base w') c.i w'.top.rootKey (X i) ∨
              w'.nodes.lookup (X i) = some ((Nn i).toPrev (c.i - 1))) ∧
            (∀ z, w.next ≤ z → (w'.nodes.lookup z).isSome = true →
              TReach (wNode c.p base w') c.i w'.top.rootKey z))) := by
    intro hmade hcs
    refine writerWP_mono (writerWP_handleFullWith_timeInPlace_termL _ D (X (D + 1))
      (X D) (Nn (D + 1)) (Nn D) last compact c w hlk hlq hpq hmade hcs) ?_
    rintro _ w' ⟨h't, h'top, h'v, h'next, h'path, h'n⟩
    have hN' : wNode c.p base w' = updN (wNode c.p base w) (X (D + 1)) (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode) :=
      wNode_upsert_updN c.p base w w' _ _ h'n h't htk
    refine ⟨by rw [hN', h'top]; exact hV, ⟨Or.inl h'top, h't, h'path, by omega, h'v⟩, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_⟩
    · intro z _ hzX
      rw [h'n, lookup_upsert, ite_eq_right_of_eq_false _ _ (eq_false (hzX _ (by omega) (Nat.le_refl _)))]
    · intro z hz
      rw [hN', h'top] at hz
      exact Or.inl hz
    · intro z zn h
      rw [hN'] at h
      by_cases hz : z = X (D + 1)
      · rw [hz, updN_self] at h; cases h; exact hlwf
      · rw [updN_ne _ _ _ _ hz] at h; exact hW z zn h
    · intro Val _ _ key
      rw [hN', h'top]
    · intro _ n hn cv y hk
      rw [hN', updN_self] at hn
      cases hn
      exact hk
    · intro _ _ z hz _
      rw [hN', h'top]; exact hz
    · intro _ _
      refine ⟨fun i h1 h2 => Or.inl ?_, fun z hz h => ?_⟩
      · rw [hN', h'top]
        rcases Nat.lt_or_ge i (D + 1) with hlt | hge
        · exact hanc _ i h1 (by omega)
        · have : i = D + 1 := by omega
          subst this
          exact TReach.link hqR ⟨_, hVq, hkl⟩
      · exfalso
        have hzX : ¬ z = X (D + 1) := by
          have := hXlt (D + 1) (by omega) (Nat.le_refl _); omega
        rw [h'n, lookup_upsert, ite_eq_right_of_eq_false _ _ (eq_false hzX), (hS5 z hz).1] at h
        simp at h
  have hSI : (Nn (D + 1)).firstTime = some c.i → (Nn D).leaf = false →
      c.p.splitAbove < last.size →
      WriterWP (handleFullWith (fun q more => appendKlongs D q more) (D + 1)
        (X (D + 1)) [] last false) c w (fun _ w' =>
        TreeOK (wNode c.p base w') c.i w'.top.rootKey ∧
          ((w'.top = w.top ∨ (s = 0 ∧ w.next ≤ w'.top.rootKey)) ∧ w'.taken = w.taken ∧ w'.path = w.path ∧
            w.next ≤ w'.next ∧ w'.vals = w.vals) ∧
          (∀ z, z < w.next → (∀ i, s ≤ i → i ≤ D + 1 → z ≠ X i) → w'.nodes.lookup z = w.nodes.lookup z) ∧
          (∀ z, TReach (wNode c.p base w') c.i w'.top.rootKey z →
            TReach (updN (wNode c.p base w) (X (D + 1)) (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode)) c.i w.top.rootKey z ∨ (w.next ≤ z ∧ z < w'.next)) ∧
          (∀ z zn, wNode c.p base w' z = some zn → klongsWf zn.ks = true) ∧
          (∀ Val : NodeId → Option Nat, (∀ z, (w.next ≤ z ∨ ∃ i, s ≤ i ∧ i ≤ D + 1 ∧ z = X i) → Val z = none) →
            (SegFits (wNode c.p base w') c.i (fuelR - 1) w'.top.rootKey ∨
              (ChainNoNewRoot c Nn s D ∧ LevelNoRoot c Nn D last compact)) →
            ∀ key, getFromR (wNode c.p base w') Val c.i fuelR key w'.top.rootKey =
              getFromR (updN (wNode c.p base w) (X (D + 1)) (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode)) Val c.i fuelR key w.top.rootKey) ∧
          (TReach (wNode c.p base w') c.i w'.top.rootKey (X (D + 1)) →
            ∀ n, wNode c.p base w' (X (D + 1)) = some n → ∀ cv y, Klong.key cv y ∈ n.ks →
              Klong.key cv y ∈ last.ks) ∧
          ((∀ i, s < i → i ≤ D → ChainOrd c K Nn i) → LastOrd c K Nn D last →
            ∀ z, TReach (updN (wNode c.p base w) (X (D + 1)) (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode)) c.i
              w.top.rootKey z → (∀ i, s ≤ i → i ≤ D + 1 → z ≠ X i) →
              TReach (wNode c.p base w') c.i w'.top.rootKey z) ∧
          ((∀ i, s < i → i ≤ D → ChainOrd c K Nn i) → LastOrd c K Nn D last →
            (∀ i, s ≤ i → i ≤ D + 1 → TReach (wNode c.p base w') c.i w'.top.rootKey (X i) ∨
              w'.nodes.lookup (X i) = some ((Nn i).toPrev (c.i - 1))) ∧
            (∀ z, w.next ≤ z → (w'.nodes.lookup z).isSome = true →
              TReach (wNode c.p base w') c.i w'.top.rootKey z))) := by
    intro hmade hqlf' hsp
    have hqlf : ¬ (Nn D).leaf = true := by simp [hqlf']
    -- a space split in place below an inner node: the second half linked from the parent
    have h2l := hlen2 hsp
    obtain ⟨r, hdiv0, hsc, hrm, hfh0, hsh0⟩ := halves_facts_nil c.i (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode) h2l hlt
    have hhalf0 := halves_read_nil c.i (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode) h2l hlt hlwf
    have hwh0 := halves_newKlongs_wf (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode).leaf c.i (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode).live []
    rw [← KNode.lastVersion_eq_newKlongs] at hwh0
    have hcov0 := halves_cover_nil c.i (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode) h2l hlt hlwf
    rw [hlastV] at hdiv0 hfh0 hsh0 hhalf0 hwh0 hcov0
    have hdiv : (halves (Nn (D + 1)).leaf c.i last []).2.2 = r.1 := hdiv0
    have hf : ∀ c' z, (c', z) ∈ (halves (Nn (D + 1)).leaf c.i last []).1.liveAt c.i → c' < r.1 ∧
        (c', z) ∈ (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode).liveAt c.i := hfh0
    have hs : ∀ c' z, (c', z) ∈ (halves (Nn (D + 1)).leaf c.i last []).2.1.liveAt c.i →
        ∃ c0, r.1 ≤ c0 ∧ c' = splitLocalCv (Nn (D + 1)).leaf r.1 c0 ∧ (c0, z) ∈ (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode).liveAt c.i := hsh0
    have hhalf : (halves (Nn (D + 1)).leaf c.i last []).1.leaf = (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode).leaf ∧
        (halves (Nn (D + 1)).leaf c.i last []).2.1.leaf = (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode).leaf ∧
        ((⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode).leaf = true → ∀ c' : Nat, c' < (halves (Nn (D + 1)).leaf c.i last []).2.2 →
          ((halves (Nn (D + 1)).leaf c.i last []).1.searchEq c.i c').map (·.y) =
            ((⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode).searchEq c.i c').map (·.y)) ∧
        ((⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode).leaf = true → ∀ c' : Nat, (halves (Nn (D + 1)).leaf c.i last []).2.2 ≤ c' →
          ((halves (Nn (D + 1)).leaf c.i last []).2.1.searchEq c.i c').map (·.y) =
            ((⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode).searchEq c.i c').map (·.y)) ∧
        ((⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode).leaf = false → ∀ c' : Nat, c' < (halves (Nn (D + 1)).leaf c.i last []).2.2 →
          ((halves (Nn (D + 1)).leaf c.i last []).1.searchLte c.i c').map (·.y) =
            ((⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode).searchLte c.i c').map (·.y)) ∧
        ((⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode).leaf = false → ∀ c' : Nat, (halves (Nn (D + 1)).leaf c.i last []).2.2 ≤ c' →
          ((halves (Nn (D + 1)).leaf c.i last []).2.1.searchLte c.i c').map (·.y) =
            ((⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode).searchLte c.i c').map (·.y)) := hhalf0
    have hwh : klongsWf (halves (Nn (D + 1)).leaf c.i last []).1.ks = true ∧
        klongsWf (halves (Nn (D + 1)).leaf c.i last []).2.1.ks = true := hwh0
    have hcov : ∀ c' z, (c', z) ∈ (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode).liveAt c.i →
        (c' < (halves (Nn (D + 1)).leaf c.i last []).2.2 →
          ∃ c'', (c'', z) ∈ (halves (Nn (D + 1)).leaf c.i last []).1.liveAt c.i) ∧
        ((halves (Nn (D + 1)).leaf c.i last []).2.2 ≤ c' →
          ∃ c'', (c'', z) ∈ (halves (Nn (D + 1)).leaf c.i last []).2.1.liveAt c.i) := hcov0
    have hql' : (Nn D).leaf = false := by simpa using hqlf
    have hrK := hrangeL hsp hql' r.1 r.2 hrm hsc
    have hXj := hXlt (D + 1) (by omega) (Nat.le_refl _)
    have hXq := hXlt D (by omega) (by omega)
    apply writerWP_handleFullWith_spaceInPlace_up_last D (X (D + 1)) (X D)
      (Nn (D + 1)) (Nn D) last c w hlk hlq (by simpa using hqlf) hmade hsp hpq hXj
    intro w1 h1n h1t h1top h1path h1next h1vals
    obtain ⟨out, hout⟩ : ∃ o, halves (Nn (D + 1)).leaf c.i
        last [] = o := ⟨_, rfl⟩
    rw [hout] at h1n hdiv hf hs hhalf hwh hcov ⊢
    rw [hdiv] at hhalf hcov
    rw [hdiv]
    have hN1 : wNode c.p base w1 = updN (updN (wNode c.p base w) (X (D + 1)) out.1)
        w.next out.2.1 :=
      wNode_two_updN c.p base w w1 _ _ _ _ h1n h1t (by omega) htk htk0
    have hVS : ¬ TReach (updN (wNode c.p base w) (X (D + 1))
        ((⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode)))
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
        ((⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode)))
      (updN (wNode c.p base w1) (X D) ([(r.1, w.next)].foldl
        (fun n (cv, y) => n.add c.i (.key cv y)) (Nn D)))
      c.i w.top.rootKey (X D) (X (D + 1)) w.next
      (Nn D) ((⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode))
      out.1 out.2.1
      ([(r.1, w.next)].foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn D))
      (K (D + 1)) r.1 (splitLocalCv (Nn (D + 1)).leaf r.1) hV hqR
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
    have hpar := hchain w1 [(r.1, w.next)] (Or.inl ⟨_, _, rfl⟩)
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
      (fun h0 hnr => by rw [h1top]; exact hR0 h0 hnr)
      (by
        intro z zn h
        rw [hN1] at h
        by_cases hz2 : z = w.next
        · rw [hz2, updN_self] at h; cases h; exact hwh.2
        · rw [updN_ne _ _ _ _ hz2] at h
          by_cases hz1 : z = X (D + 1)
          · rw [hz1, updN_self] at h; cases h; exact hwh.1
          · rw [updN_ne _ _ _ _ hz1] at h; exact hW z zn h)
      (by rw [h1top]; exact hT2)
    refine writerWP_mono hpar ?_
    rintro _ w2 ⟨hT2', ⟨h2top, h2t, h2path, h2next, h2vals⟩, h2frame, h2reach, h2W, h2R, _,
      h2RB, h2RN⟩
    refine ⟨hT2', ⟨?_, by rw [h2t, h1t], by rw [h2path, h1path], by omega,
      by rw [h2vals, h1vals]⟩, ?_, ?_, h2W, ?_, ?_, ?_, ?_⟩
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
        · exact Or.inl h''
        · exact Or.inr (by omega)
      · exact Or.inr (by omega)
    · intro Val hVal hfit key
      rw [h2R Val (fun z hz => hVal z (by
        rcases hz with h | ⟨i, h1, h2, h3⟩
        · exact Or.inl (by omega)
        · exact Or.inr ⟨i, h1, by omega, h3⟩))
        (hfit.imp id (fun hf => hf.1)) key, h1top]
      have hXqj : X (D + 1) ≠ X D := fun h => hqx h.symm
      have hXjn : X (D + 1) ≠ w.next := by omega
      exact getFromR_spaceInPlaceLevel _ _ Val c.i fuelR w.top.rootKey (X D)
        (X (D + 1)) w.next (Nn D) _ out.1 out.2.1 (K (D + 1)) r.1 hV hwfV hVq
        hrqV hql' hqwf hqtimes hkl hqx hrK.1
        (fun c' z hcz => by
          by_cases hle : c' ≤ K (D + 1)
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
    · intro _ n hn cv y hk
      have hXjD : ∀ i, s ≤ i → i ≤ D → X (D + 1) ≠ X i := by
        intro i h1 h2 he
        have := hdist _ _ (by omega) (Nat.le_refl _) h1 (by omega) he; omega
      have hlk2 : w2.nodes.lookup (X (D + 1)) = some out.1 := by
        rw [h2frame _ (by omega) hXjD, h1n]
        simp only [↓reduceIte]
      have htk2 : w2.taken.contains (X (D + 1)) = false := by rw [h2t, h1t]; exact htk
      have hn2 : wNode c.p base w2 (X (D + 1)) = some out.1 := by
        simp only [wNode, htk2, Bool.false_eq_true, ↓reduceIte, hlk2]
      rw [hn2] at hn
      cases hn
      rw [← hout] at hk
      exact halves_nil_first_keys _ _ _ cv y hk
    · intro hHS hLO z hz hzx
      have hKr := lastOrd_div c K Nn D last hLO hql' hsp hlastV h2l
      rw [hout, hdiv] at hKr
      have hXjn : X (D + 1) ≠ w.next := by omega
      have hRq : TReach (updN (updN (wNode c.p base w) (X (D + 1)) out.1) w.next out.2.1) c.i
          w.top.rootKey (X D) :=
        tReach_to_agree _ _ c.i _ hagree1 _ (hanc out.1 D (by omega) (Nat.le_refl _))
      have hRq' := tReach_updN_self _ c.i _ _ ([(r.1, w.next)].foldl
        (fun n (cv, y) => n.add c.i (.key cv y)) (Nn D)) hT1 hRq
      have hmemX : (K (D + 1), X (D + 1)) ∈ ([(r.1, w.next)].foldl
          (fun n (cv, y) => n.add c.i (.key cv y)) (Nn D)).liveAt c.i :=
        addKeys_liveAt_keep c.i _ _ hqwf hqtimes _ _ hkl (fun q hq => by
          simp only [List.mem_singleton] at hq; subst hq; simp only; omega)
      have hmemS : (r.1, w.next) ∈ ([(r.1, w.next)].foldl
          (fun n (cv, y) => n.add c.i (.key cv y)) (Nn D)).liveAt c.i :=
        KNode.add_key_liveAt_self _ c.i _ _ hqwf hqtimes
      have hXr := TReach.link hRq' ⟨_, updN_self _ _ _, hmemX⟩
      have hSr := TReach.link hRq' ⟨_, updN_self _ _ _, hmemS⟩
      have hne : ∀ c' z', (c', z') ∈ (Nn D).liveAt c.i → z' ≠ X (D + 1) → r.1 ≠ c' := by
        intro c' z' hc hz' he
        subst he
        rcases Nat.lt_or_ge (K (D + 1)) r.1 with h | h
        · have := hrK.2 r.1 z' (by
            have h' := hc; rw [KNode.liveAt_of_times _ c.i hqtimes] at h'; simpa using h') h
          omega
        · omega
      have hz1 : TReach (updN (updN (updN (wNode c.p base w) (X (D + 1)) out.1) w.next out.2.1)
          (X D) ([(r.1, w.next)].foldl (fun n (cv, y) => n.add c.i (.key cv y))
            (Nn D))) c.i w.top.rootKey z :=
        tReach_transport _ _ c.i w.top.rootKey w.top.rootKey (X (D + 1)) _ (updN_self _ _ _)
          (fun _ => TReach.root)
          (fun u c' z' hu hux _ hl hzx' => by
            obtain ⟨mm, hm, hc⟩ := hl
            by_cases huq : u = X D
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
      exact h2RB hHS z (by rw [hN1, h1top]; exact hz1)
        (fun i h1 h2 => hzx i h1 (by omega))
    · intro hHS hLO
      have hKr := lastOrd_div c K Nn D last hLO hql' hsp hlastV h2l
      rw [hout, hdiv] at hKr
      have hXjn : X (D + 1) ≠ w.next := by omega
      have hRq : TReach (updN (updN (wNode c.p base w) (X (D + 1)) out.1) w.next out.2.1) c.i
          w.top.rootKey (X D) :=
        tReach_to_agree _ _ c.i _ hagree1 _ (hanc out.1 D (by omega) (Nat.le_refl _))
      have hRq' := tReach_updN_self _ c.i _ _ ([(r.1, w.next)].foldl
        (fun n (cv, y) => n.add c.i (.key cv y)) (Nn D)) hT1 hRq
      have hmemX : (K (D + 1), X (D + 1)) ∈ ([(r.1, w.next)].foldl
          (fun n (cv, y) => n.add c.i (.key cv y)) (Nn D)).liveAt c.i :=
        addKeys_liveAt_keep c.i _ _ hqwf hqtimes _ _ hkl (fun q hq => by
          simp only [List.mem_singleton] at hq; subst hq; simp only; omega)
      have hmemS : (r.1, w.next) ∈ ([(r.1, w.next)].foldl
          (fun n (cv, y) => n.add c.i (.key cv y)) (Nn D)).liveAt c.i :=
        KNode.add_key_liveAt_self _ c.i _ _ hqwf hqtimes
      have hXr := TReach.link hRq' ⟨_, updN_self _ _ _, hmemX⟩
      have hSr := TReach.link hRq' ⟨_, updN_self _ _ _, hmemS⟩
      obtain ⟨hR2c, hR3c⟩ := h2RN hHS
      refine ⟨fun i h1 h2 => ?_, fun z hz h => ?_⟩
      · rcases Nat.lt_or_ge i (D + 1) with hlt | hge
        · exact hR2c i h1 (by omega)
        · left
          have : i = D + 1 := by omega
          subst this
          exact h2RB hHS _ (by rw [hN1, h1top]; exact hXr)
            (fun i h1 h2 he => by
              have := hdist _ _ h1 (by omega) (by omega) (Nat.le_refl _) he.symm; omega)
      · rcases Nat.lt_or_ge z w1.next with hlt | hge
        · have hzX : ¬ z = X (D + 1) := by omega
          have h1' : (w1.nodes.lookup z).isSome = true := by
            rw [← h2frame z hlt (fun i h1 h2 he => by have := hXlt i h1 (by omega); omega)]
            exact h
          have hzn : z = w.next := by
            refine Classical.byContradiction (fun hne => ?_)
            rw [h1n] at h1'
            simp only [hzX, hne, ↓reduceIte, (hS5 z hz).1, Option.isSome_none,
              Bool.false_eq_true] at h1'
          subst hzn
          exact h2RB hHS _ (by rw [hN1, h1top]; exact hSr)
            (fun i h1 h2 he => by have := hXlt i h1 (by omega); omega)
        · exact hR3c z hge h

  have hSEG : compact = false → (Nn (D + 1)).firstTime ≠ some c.i → (Nn D).leaf = true →
      c.p.splitAbove < last.size →
      WriterWP (handleFullWith (fun q more => appendKlongs D q more) (D + 1)
        (X (D + 1)) [] last false) c w (fun _ w' =>
        TreeOK (wNode c.p base w') c.i w'.top.rootKey ∧
          ((w'.top = w.top ∨ (s = 0 ∧ w.next ≤ w'.top.rootKey)) ∧ w'.taken = w.taken ∧ w'.path = w.path ∧
            w.next ≤ w'.next ∧ w'.vals = w.vals) ∧
          (∀ z, z < w.next → (∀ i, s ≤ i → i ≤ D + 1 → z ≠ X i) → w'.nodes.lookup z = w.nodes.lookup z) ∧
          (∀ z, TReach (wNode c.p base w') c.i w'.top.rootKey z →
            TReach (updN (wNode c.p base w) (X (D + 1)) (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode)) c.i w.top.rootKey z ∨ (w.next ≤ z ∧ z < w'.next)) ∧
          (∀ z zn, wNode c.p base w' z = some zn → klongsWf zn.ks = true) ∧
          (∀ Val : NodeId → Option Nat, (∀ z, (w.next ≤ z ∨ ∃ i, s ≤ i ∧ i ≤ D + 1 ∧ z = X i) → Val z = none) →
            (SegFits (wNode c.p base w') c.i (fuelR - 1) w'.top.rootKey ∨
              (ChainNoNewRoot c Nn s D ∧ LevelNoRoot c Nn D last compact)) →
            ∀ key, getFromR (wNode c.p base w') Val c.i fuelR key w'.top.rootKey =
              getFromR (updN (wNode c.p base w) (X (D + 1)) (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode)) Val c.i fuelR key w.top.rootKey) ∧
          (TReach (wNode c.p base w') c.i w'.top.rootKey (X (D + 1)) →
            ∀ n, wNode c.p base w' (X (D + 1)) = some n → ∀ cv y, Klong.key cv y ∈ n.ks →
              Klong.key cv y ∈ last.ks) ∧
          ((∀ i, s < i → i ≤ D → ChainOrd c K Nn i) → LastOrd c K Nn D last →
            ∀ z, TReach (updN (wNode c.p base w) (X (D + 1)) (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode)) c.i
              w.top.rootKey z → (∀ i, s ≤ i → i ≤ D + 1 → z ≠ X i) →
              TReach (wNode c.p base w') c.i w'.top.rootKey z) ∧
          ((∀ i, s < i → i ≤ D → ChainOrd c K Nn i) → LastOrd c K Nn D last →
            (∀ i, s ≤ i → i ≤ D + 1 → TReach (wNode c.p base w') c.i w'.top.rootKey (X i) ∨
              w'.nodes.lookup (X i) = some ((Nn i).toPrev (c.i - 1))) ∧
            (∀ z, w.next ≤ z → (w'.nodes.lookup z).isSome = true →
              TReach (wNode c.p base w') c.i w'.top.rootKey z))) := by
    intro hcf hmade hqlf hsp
    -- a space split below a leaf, the node not made: a new segment root above the halves
    have hord : ∀ i', s < i' → i' < D + 1 → ChainOrd c K Nn i' := by
      rcases hspaceL (by rw [hcf]; simpa using hsp) with h | h
      · rw [hqlf] at h; cases h
      · exact h hmade
    have hfuel4 : 2 ≤ fuelR := hfR
    have h2l := hlen2 hsp
    obtain ⟨r, hdiv0, hsc, hrm, hfh0, hsh0⟩ := halves_facts_nil c.i (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode) h2l hlt
    have hhalf0 := halves_read_nil c.i (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode) h2l hlt hlwf
    have hwh0 := halves_newKlongs_wf (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode).leaf c.i (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode).live []
    rw [← KNode.lastVersion_eq_newKlongs] at hwh0
    have hcov0 := halves_cover_nil c.i (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode) h2l hlt hlwf
    rw [hlastV] at hdiv0 hfh0 hsh0 hhalf0 hwh0 hcov0
    have hdiv : (halves (Nn (D + 1)).leaf c.i last []).2.2 = r.1 := hdiv0
    have hf : ∀ c' z, (c', z) ∈ (halves (Nn (D + 1)).leaf c.i last []).1.liveAt c.i → c' < r.1 ∧
        (c', z) ∈ (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode).liveAt c.i := hfh0
    have hs : ∀ c' z, (c', z) ∈ (halves (Nn (D + 1)).leaf c.i last []).2.1.liveAt c.i →
        ∃ c0, r.1 ≤ c0 ∧ c' = splitLocalCv (Nn (D + 1)).leaf r.1 c0 ∧ (c0, z) ∈ (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode).liveAt c.i := hsh0
    have hhalf : (halves (Nn (D + 1)).leaf c.i last []).1.leaf = (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode).leaf ∧
        (halves (Nn (D + 1)).leaf c.i last []).2.1.leaf = (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode).leaf ∧
        ((⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode).leaf = true → ∀ c' : Nat, c' < (halves (Nn (D + 1)).leaf c.i last []).2.2 →
          ((halves (Nn (D + 1)).leaf c.i last []).1.searchEq c.i c').map (·.y) =
            ((⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode).searchEq c.i c').map (·.y)) ∧
        ((⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode).leaf = true → ∀ c' : Nat, (halves (Nn (D + 1)).leaf c.i last []).2.2 ≤ c' →
          ((halves (Nn (D + 1)).leaf c.i last []).2.1.searchEq c.i c').map (·.y) =
            ((⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode).searchEq c.i c').map (·.y)) ∧
        ((⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode).leaf = false → ∀ c' : Nat, c' < (halves (Nn (D + 1)).leaf c.i last []).2.2 →
          ((halves (Nn (D + 1)).leaf c.i last []).1.searchLte c.i c').map (·.y) =
            ((⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode).searchLte c.i c').map (·.y)) ∧
        ((⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode).leaf = false → ∀ c' : Nat, (halves (Nn (D + 1)).leaf c.i last []).2.2 ≤ c' →
          ((halves (Nn (D + 1)).leaf c.i last []).2.1.searchLte c.i c').map (·.y) =
            ((⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode).searchLte c.i c').map (·.y)) := hhalf0
    have hwh : klongsWf (halves (Nn (D + 1)).leaf c.i last []).1.ks = true ∧
        klongsWf (halves (Nn (D + 1)).leaf c.i last []).2.1.ks = true := hwh0
    have hcov : ∀ c' z, (c', z) ∈ (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode).liveAt c.i →
        (c' < (halves (Nn (D + 1)).leaf c.i last []).2.2 →
          ∃ c'', (c'', z) ∈ (halves (Nn (D + 1)).leaf c.i last []).1.liveAt c.i) ∧
        ((halves (Nn (D + 1)).leaf c.i last []).2.2 ≤ c' →
          ∃ c'', (c'', z) ∈ (halves (Nn (D + 1)).leaf c.i last []).2.1.liveAt c.i) := hcov0
    apply writerWP_handleFullWith_segSpace_upL D (X (D + 1)) (X D)
      (Nn (D + 1)) (Nn D) last (K (D + 1)) [] c w hlk hlq hqlf hmade hsp hpq hpk
    intro w1 h1n h1t h1top h1path h1next h1vals
    obtain ⟨out, hout⟩ : ∃ o, halves (Nn (D + 1)).leaf c.i
        last [] = o := ⟨_, rfl⟩
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
    have hXj := hXlt (D + 1) (by omega) (Nat.le_refl _)
    have hXq := hXlt D (by omega) (by omega)
    obtain ⟨hT2, hR2⟩ := treeOK_segSpaceStep
      (updN (wNode c.p base w) (X (D + 1))
        ((⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode)))
      (updN (wNode c.p base w1) (X D) ([(K (D + 1), w.next + 2 + 2)].foldl
        (fun n (cv, y) => n.add c.i (.key cv y)) (Nn D)))
      c.i w.top.rootKey (X D) (X (D + 1)) w.next (w.next + 2) (w.next + 2 + 2)
      (Nn D) ((⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode))
      out.1 out.2.1 ⟨false, [.time c.i, .key 0 w.next, .key r.1 (w.next + 2)]⟩
      ([(K (D + 1), w.next + 2 + 2)].foldl
        (fun n (cv, y) => n.add c.i (.key cv y)) (Nn D))
      (K (D + 1)) r.1 (splitLocalCv (Nn (D + 1)).leaf r.1) hsc hV hqR
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
            ⟨K (D + 1), KNode.add_key_liveAt_self _ c.i _ _ hqwf hqtimes⟩ (by omega)
          exact getFromR_segSpaceLevel _ _ Val c.i fuelR hfuel4 w.top.rootKey (X D)
            (X (D + 1)) w.next (w.next + 2) (w.next + 2 + 2) (Nn D) _ out.1 out.2.1
            (K (D + 1)) r.1 hV hwfV hVq hrqV hqlf hqwf hqtimes hkl hqx (updN_self _ _ _)
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
        · exact absurd (hNo (by rw [hcf]; simpa using hsp)) (by rw [hqlf]; simp))
      (by
        intro _ _ z hz hzx
        have hqR' := tReach_updN_self _ c.i _ _ ([(K (D + 1), w.next + 2 + 2)].foldl
          (fun n (cv, y) => n.add c.i (.key cv y)) (Nn D))
          (treeOK_of_agree _ _ _ _ hS3 hagree)
          (tReach_to_agree _ _ _ _ hagree _ (hS4 D (by omega) (by omega)))
        have hR' := TReach.link hqR' ⟨_, updN_self _ _ _,
          KNode.add_key_liveAt_self _ c.i _ _ hqwf hqtimes⟩
        have hRoot := rootPair_liveAt c.i w.next (w.next + 2) r.1 hsc
        have hRn : (updN (wNode c.p base w1) (X D) ([(K (D + 1), w.next + 2 + 2)].foldl
            (fun n (cv, y) => n.add c.i (.key cv y)) (Nn D))) (w.next + 2 + 2) =
            some ⟨false, newKlongs c.i [(0, w.next), (r.1, w.next + 2)]⟩ := by
          rw [updN_ne _ _ _ _ (hQn _ (by omega)), hN1, updN_self]; rfl
        have hFr := TReach.link hR' ⟨_, hRn, hRoot.1⟩
        have hSr := TReach.link hR' ⟨_, hRn, hRoot.2⟩
        refine tReach_transport _ _ c.i w.top.rootKey w.top.rootKey (X (D + 1)) _
          (updN_self _ _ _) ?_ ?_ ?_ z hz hzx
        · exact (fun _ => TReach.root)
        · intro u c' z' hu hux _ hl hzx'
          obtain ⟨mm, hm, hc⟩ := hl
          by_cases huq : u = X D
          · subst huq
            rw [updN_ne _ _ _ _ hqx, hwq] at hm
            cases hm
            exact ⟨_, updN_self _ _ _, insOK_keep c.i _ _ (Or.inl ⟨_, _, rfl⟩) (K (D + 1))
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
        intro _ _ z hz hlt h
        have hqR' := tReach_updN_self _ c.i _ _ ([(K (D + 1), w.next + 2 + 2)].foldl
          (fun n (cv, y) => n.add c.i (.key cv y)) (Nn D))
          (treeOK_of_agree _ _ _ _ hS3 hagree)
          (tReach_to_agree _ _ _ _ hagree _ (hS4 D (by omega) (by omega)))
        have hR' := TReach.link hqR' ⟨_, updN_self _ _ _,
          KNode.add_key_liveAt_self _ c.i _ _ hqwf hqtimes⟩
        have hRoot := rootPair_liveAt c.i w.next (w.next + 2) r.1 hsc
        have hRn : (updN (wNode c.p base w1) (X D) ([(K (D + 1), w.next + 2 + 2)].foldl
            (fun n (cv, y) => n.add c.i (.key cv y)) (Nn D))) (w.next + 2 + 2) =
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

  have hSSIP : compact = false → (Nn (D + 1)).firstTime = some c.i → (Nn D).leaf = true →
      c.p.splitAbove < last.size →
      WriterWP (handleFullWith (fun q more => appendKlongs D q more) (D + 1)
        (X (D + 1)) [] last false) c w (fun _ w' =>
        TreeOK (wNode c.p base w') c.i w'.top.rootKey ∧
          ((w'.top = w.top ∨ (s = 0 ∧ w.next ≤ w'.top.rootKey)) ∧ w'.taken = w.taken ∧ w'.path = w.path ∧
            w.next ≤ w'.next ∧ w'.vals = w.vals) ∧
          (∀ z, z < w.next → (∀ i, s ≤ i → i ≤ D + 1 → z ≠ X i) → w'.nodes.lookup z = w.nodes.lookup z) ∧
          (∀ z, TReach (wNode c.p base w') c.i w'.top.rootKey z →
            TReach (updN (wNode c.p base w) (X (D + 1)) (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode)) c.i w.top.rootKey z ∨ (w.next ≤ z ∧ z < w'.next)) ∧
          (∀ z zn, wNode c.p base w' z = some zn → klongsWf zn.ks = true) ∧
          (∀ Val : NodeId → Option Nat, (∀ z, (w.next ≤ z ∨ ∃ i, s ≤ i ∧ i ≤ D + 1 ∧ z = X i) → Val z = none) →
            (SegFits (wNode c.p base w') c.i (fuelR - 1) w'.top.rootKey ∨
              (ChainNoNewRoot c Nn s D ∧ LevelNoRoot c Nn D last compact)) →
            ∀ key, getFromR (wNode c.p base w') Val c.i fuelR key w'.top.rootKey =
              getFromR (updN (wNode c.p base w) (X (D + 1)) (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode)) Val c.i fuelR key w.top.rootKey) ∧
          (TReach (wNode c.p base w') c.i w'.top.rootKey (X (D + 1)) →
            ∀ n, wNode c.p base w' (X (D + 1)) = some n → ∀ cv y, Klong.key cv y ∈ n.ks →
              Klong.key cv y ∈ last.ks) ∧
          ((∀ i, s < i → i ≤ D → ChainOrd c K Nn i) → LastOrd c K Nn D last →
            ∀ z, TReach (updN (wNode c.p base w) (X (D + 1)) (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode)) c.i
              w.top.rootKey z → (∀ i, s ≤ i → i ≤ D + 1 → z ≠ X i) →
              TReach (wNode c.p base w') c.i w'.top.rootKey z) ∧
          ((∀ i, s < i → i ≤ D → ChainOrd c K Nn i) → LastOrd c K Nn D last →
            (∀ i, s ≤ i → i ≤ D + 1 → TReach (wNode c.p base w') c.i w'.top.rootKey (X i) ∨
              w'.nodes.lookup (X i) = some ((Nn i).toPrev (c.i - 1))) ∧
            (∀ z, w.next ≤ z → (w'.nodes.lookup z).isSome = true →
              TReach (wNode c.p base w') c.i w'.top.rootKey z))) := by
    intro hcf hmade hqlf hsp
    -- a space split in place below a leaf: a new segment root above, the leaf repointed
    have hfuel4 : 2 ≤ fuelR := hfR
    have h2l := hlen2 hsp
    obtain ⟨r, hdiv0, hsc, _, hfh0, hsh0⟩ := halves_facts_nil c.i (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode) h2l hlt
    have hhalf0 := halves_read_nil c.i (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode) h2l hlt hlwf
    have hwh0 := halves_newKlongs_wf (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode).leaf c.i (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode).live []
    rw [← KNode.lastVersion_eq_newKlongs] at hwh0
    have hcov0 := halves_cover_nil c.i (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode) h2l hlt hlwf
    rw [hlastV] at hdiv0 hfh0 hsh0 hhalf0 hwh0 hcov0
    have hdiv : (halves (Nn (D + 1)).leaf c.i last []).2.2 = r.1 := hdiv0
    have hf : ∀ c' z, (c', z) ∈ (halves (Nn (D + 1)).leaf c.i last []).1.liveAt c.i → c' < r.1 ∧
        (c', z) ∈ (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode).liveAt c.i := hfh0
    have hs : ∀ c' z, (c', z) ∈ (halves (Nn (D + 1)).leaf c.i last []).2.1.liveAt c.i →
        ∃ c0, r.1 ≤ c0 ∧ c' = splitLocalCv (Nn (D + 1)).leaf r.1 c0 ∧ (c0, z) ∈ (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode).liveAt c.i := hsh0
    have hhalf : (halves (Nn (D + 1)).leaf c.i last []).1.leaf = (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode).leaf ∧
        (halves (Nn (D + 1)).leaf c.i last []).2.1.leaf = (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode).leaf ∧
        ((⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode).leaf = true → ∀ c' : Nat, c' < (halves (Nn (D + 1)).leaf c.i last []).2.2 →
          ((halves (Nn (D + 1)).leaf c.i last []).1.searchEq c.i c').map (·.y) =
            ((⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode).searchEq c.i c').map (·.y)) ∧
        ((⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode).leaf = true → ∀ c' : Nat, (halves (Nn (D + 1)).leaf c.i last []).2.2 ≤ c' →
          ((halves (Nn (D + 1)).leaf c.i last []).2.1.searchEq c.i c').map (·.y) =
            ((⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode).searchEq c.i c').map (·.y)) ∧
        ((⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode).leaf = false → ∀ c' : Nat, c' < (halves (Nn (D + 1)).leaf c.i last []).2.2 →
          ((halves (Nn (D + 1)).leaf c.i last []).1.searchLte c.i c').map (·.y) =
            ((⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode).searchLte c.i c').map (·.y)) ∧
        ((⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode).leaf = false → ∀ c' : Nat, (halves (Nn (D + 1)).leaf c.i last []).2.2 ≤ c' →
          ((halves (Nn (D + 1)).leaf c.i last []).2.1.searchLte c.i c').map (·.y) =
            ((⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode).searchLte c.i c').map (·.y)) := hhalf0
    have hwh : klongsWf (halves (Nn (D + 1)).leaf c.i last []).1.ks = true ∧
        klongsWf (halves (Nn (D + 1)).leaf c.i last []).2.1.ks = true := hwh0
    have hcov : ∀ c' z, (c', z) ∈ (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode).liveAt c.i →
        (c' < (halves (Nn (D + 1)).leaf c.i last []).2.2 →
          ∃ c'', (c'', z) ∈ (halves (Nn (D + 1)).leaf c.i last []).1.liveAt c.i) ∧
        ((halves (Nn (D + 1)).leaf c.i last []).2.2 ≤ c' →
          ∃ c'', (c'', z) ∈ (halves (Nn (D + 1)).leaf c.i last []).2.1.liveAt c.i) := hcov0
    have hXj := hXlt (D + 1) (by omega) (Nat.le_refl _)
    have hXq := hXlt D (by omega) (by omega)
    refine writerWP_mono (writerWP_handleFullWith_segSpaceInPlace_termL D (X (D + 1))
      (X D) (Nn (D + 1)) (Nn D) last (K (D + 1)) [] c w hlk hlq hqx hqlf
      hmade hsp hpq hpk hXj hXq hfree2) ?_
    rintro _ w' ⟨j0, hj0, h't, h'top, h'v, h'path, h'next, h'n⟩
    obtain ⟨out, hout⟩ : ∃ o, halves (Nn (D + 1)).leaf c.i last [] = o := ⟨_, rfl⟩
    rw [hout] at h'n hdiv hf hs hhalf hwh hcov
    rw [hdiv] at h'n hhalf hcov
    obtain ⟨hq2k, hq2⟩ := KNode.repoint_link_facts (Nn D) c.i (X (D + 1))
      (w.next + 2) (K (D + 1)) j0 hj0 hqtimes
    have hjF : ¬ X (D + 1) = w.next := by omega
    have hjR : ¬ X (D + 1) = w.next + 2 := by omega
    have hqF : ¬ X D = w.next := by omega
    have hqR' : ¬ X D = w.next + 2 := by omega
    have hFj : ¬ w.next = X (D + 1) := by omega
    have hRj : ¬ w.next + 2 = X (D + 1) := by omega
    have hFq : ¬ w.next = X D := by omega
    have hRq : ¬ w.next + 2 = X D := by omega
    have hRF : ¬ w.next + 2 = w.next := by omega
    have hw' : ∀ z, wNode c.p base w' z =
        if z = X (D + 1) then some out.1
        else if z = X D then some ((Nn D).repoint j0 (w.next + 2))
        else if z = w.next then some out.2.1
        else if z = w.next + 2 then
          some ⟨false, [.time c.i, .key 0 (X (D + 1)), .key r.1 w.next]⟩
        else wNode c.p base w z := by
      intro z
      by_cases h1 : z = X (D + 1)
      · subst h1; simp only [wNode, h't, htk, h'n, Bool.false_eq_true, ↓reduceIte]
      · by_cases h2 : z = X D
        · subst h2; simp only [wNode, h't, htq, h'n, h1, Bool.false_eq_true, ↓reduceIte]
        · by_cases h3 : z = w.next
          · subst h3
            simp only [wNode, h't, htk0, h'n, h1, h2, Bool.false_eq_true, ↓reduceIte]
          · by_cases h4 : z = w.next + 2
            · subst h4
              simp only [wNode, h't, htk2', h'n, h1, h2, h3, Bool.false_eq_true, ↓reduceIte]
            · simp only [wNode, h't, h'n, h1, h2, h3, h4, ↓reduceIte]
    have hnd : ([(0, X (D + 1)), (r.1, w.next)].map Prod.fst).Nodup := by
      simp only [List.map_cons, List.map_nil, List.nodup_cons, List.mem_cons,
        List.not_mem_nil, or_false, List.nodup_nil, and_true, not_false_eq_true]
      omega
    have hrn : ∀ c' z, (c', z) ∈ (⟨false, [.time c.i, .key 0 (X (D + 1)),
        .key r.1 w.next]⟩ : KNode).liveAt c.i →
        (c' = 0 ∧ z = X (D + 1)) ∨ (c' = r.1 ∧ z = w.next) := by
      intro c' z h
      have h' := (mrg_newKlongs_liveAt_iff false c.i [(0, X (D + 1)), (r.1, w.next)]
        hnd c' z).mp h
      simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h'
      exact h'
    obtain ⟨hT2, hR2⟩ := treeOK_segSpaceInPlaceStep
      (updN (wNode c.p base w) (X (D + 1)) (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode))
      (wNode c.p base w') c.i w.top.rootKey (X D) (X (D + 1)) w.next (w.next + 2)
      (Nn D) (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode)
      out.1 out.2.1 ⟨false, [.time c.i, .key 0 (X (D + 1)), .key r.1 w.next]⟩
      ((Nn D).repoint j0 (w.next + 2))
      (K (D + 1)) r.1 (splitLocalCv (Nn (D + 1)).leaf r.1) hsc hV hqR
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
    -- q stays reached: the nodes above it are kept
    obtain ⟨aq, haq⟩ := hqR.pathLen
    have hshort : ∀ z a', PathLen (updN (wNode c.p base w) (X (D + 1))
        (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode)) c.i w.top.rootKey
        z a' → a' ≤ aq → TReach (wNode c.p base w') c.i w.top.rootKey z := by
      intro z a' hz ha'
      refine tReach_of_agree_short _ _ c.i _ a' z hz (fun x k hx hk => ?_)
      have hxq : x ≠ X D := fun he => by
        subst he; have := PathLen.depth_unique hV _ _ _ hx haq; omega
      have hxj : x ≠ X (D + 1) := fun he => by
        subst he
        have hl2 : PathLen (updN (wNode c.p base w) (X (D + 1))
            (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode)) c.i
            w.top.rootKey (X (D + 1)) (aq + 1) :=
          PathLen.link haq ⟨_, by rw [updN_ne _ _ _ _ hqx]; exact hwq, hkl⟩
        have := PathLen.depth_unique hV _ _ _ hx hl2; omega
      have hxn := hVlt x hx.reach
      rw [hw', updN_ne _ _ _ _ hxj]
      simp only [hxj, hxq, show ¬ x = w.next by omega, show ¬ x = w.next + 2 by omega, ↓reduceIte]
    have hq' : TReach (wNode c.p base w') c.i w.top.rootKey (X D) := hshort _ aq haq (Nat.le_refl _)
    have hRr : TReach (wNode c.p base w') c.i w.top.rootKey (w.next + 2) :=
      TReach.link hq' ⟨_, by rw [hw']; simp only [hqx, ↓reduceIte], hq2k⟩
    have hRoot := rootPair_liveAt c.i (X (D + 1)) w.next r.1 hsc
    have hRn : wNode c.p base w' (w.next + 2) =
        some ⟨false, newKlongs c.i [(0, X (D + 1)), (r.1, w.next)]⟩ := by
      rw [hw']; simp only [hRj, hRq, hRF, ↓reduceIte]; rfl
    have hXr : TReach (wNode c.p base w') c.i w.top.rootKey (X (D + 1)) :=
      TReach.link hRr ⟨_, hRn, hRoot.1⟩
    have hSr : TReach (wNode c.p base w') c.i w.top.rootKey w.next :=
      TReach.link hRr ⟨_, hRn, hRoot.2⟩
    have hRB0 : ∀ z, TReach (updN (wNode c.p base w) (X (D + 1))
        (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode)) c.i w.top.rootKey z →
        z ≠ X (D + 1) → TReach (wNode c.p base w') c.i w.top.rootKey z := by
      refine tReach_transport _ _ c.i w.top.rootKey w.top.rootKey (X (D + 1)) _
        (updN_self _ _ _) ?_ ?_ ?_
      · exact (fun _ => TReach.root)
      · intro u c' z' hu hux _ hl hzx'
        obtain ⟨mm, hm, hc⟩ := hl
        by_cases huq : u = X D
        · subst huq
          rw [updN_ne _ _ _ _ hqx, hwq] at hm
          cases hm
          refine ⟨(Nn D).repoint j0 (w.next + 2), by rw [hw']; simp only [hqx, ↓reduceIte], ?_⟩
          rcases Nat.lt_or_ge c' (K (D + 1)) with hlt | hge
          · rw [KNode.liveAt_of_times _ c.i (KNode.repoint_times _ _ _ c.i hqtimes),
              mem_iff_lookup _ (KNode.live_keys_nodup _),
              KNode.repoint_live_lookup _ _ _ _ _ hj0 c']
            have hb : (K (D + 1) == c') = false := by simp only [beq_eq_false_iff_ne, ne_eq]; omega
            rw [hb]; simp only [Bool.false_eq_true, ↓reduceIte]
            rw [KNode.liveAt_of_times _ c.i hqtimes] at hc
            exact lookup_of_mem_nodup _ (KNode.live_keys_nodup _) _ _ hc
          · have hcK : c' ≠ K (D + 1) := fun he => by
              subst he; exact hzx' (liveAt_cv_unique _ c.i hqtimes _ _ _ hc hkl)
            rw [KNode.liveAt_of_times _ c.i (KNode.repoint_times _ _ _ c.i hqtimes),
              mem_iff_lookup _ (KNode.live_keys_nodup _),
              KNode.repoint_live_lookup _ _ _ _ _ hj0 c']
            have hb : (K (D + 1) == c') = false := by
              simp only [beq_eq_false_iff_ne, ne_eq]; exact fun h => hcK h.symm
            rw [hb]; simp only [Bool.false_eq_true, ↓reduceIte]
            rw [KNode.liveAt_of_times _ c.i hqtimes] at hc
            exact lookup_of_mem_nodup _ (KNode.live_keys_nodup _) _ _ hc
        · have hu0 := hVlt u hu
          rw [updN_ne _ _ _ _ hux] at hm
          refine ⟨mm, ?_, hc⟩
          rw [hw']
          simp only [hux, huq, show ¬ u = w.next by omega, show ¬ u = w.next + 2 by omega, ↓reduceIte]
          exact hm
      · intro c' z' hc
        obtain ⟨hFc, hSc⟩ := hcov c' z' hc
        by_cases hlt : c' < r.1
        · obtain ⟨c'', h''⟩ := hFc hlt
          exact TReach.link hXr ⟨out.1, by rw [hw']; simp only [↓reduceIte], h''⟩
        · obtain ⟨c'', h''⟩ := hSc (by omega)
          exact TReach.link hSr ⟨out.2.1, by rw [hw']; simp only [hFj, hFq, ↓reduceIte], h''⟩
    refine ⟨by rw [h'top]; exact hT2, ⟨Or.inl h'top, h't, h'path, by omega, h'v⟩, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_⟩
    · intro z hz hzX
      rw [h'n]
      have h1' : ¬ z = X (D + 1) := hzX _ (by omega) (Nat.le_refl _)
      have h2' : ¬ z = X D := hzX _ (by omega) (by omega)
      have h3' : ¬ z = w.next := by omega
      have h4' : ¬ z = w.next + 2 := by omega
      simp only [h1', h2', h3', h4', ↓reduceIte]
    · intro z hz
      rw [h'top] at hz
      rcases hR2 z hz with h | h | h
      · exact Or.inl h
      · exact Or.inr ⟨by omega, by omega⟩
      · exact Or.inr ⟨by omega, by omega⟩
    · intro z zn h
      rw [hw'] at h
      by_cases h1 : z = X (D + 1)
      · subst h1; simp only [↓reduceIte, Option.some.injEq] at h; subst h; exact hwh.1
      · by_cases h2 : z = X D
        · subst h2; simp only [h1, ↓reduceIte, Option.some.injEq] at h; subst h
          rw [KNode.repoint_klongsWf]; exact hqwf
        · by_cases h3 : z = w.next
          · subst h3; simp only [h1, h2, ↓reduceIte, Option.some.injEq] at h; subst h
            exact hwh.2
          · by_cases h4 : z = w.next + 2
            · subst h4; simp only [h1, h2, h3, ↓reduceIte, Option.some.injEq] at h; subst h
              exact klongsWf_newKlongs c.i [(0, X (D + 1)), (r.1, w.next)]
            · simp only [h1, h2, h3, h4, ↓reduceIte] at h; exact hW z zn h
    · intro Val hVal hfit key
      rcases hfit with hf' | hNo
      · rw [h'top] at hf' ⊢
        have hdR := hf' _ (tReach_reachS _ _ _ _ hRr)
        exact getFromR_segSpaceInPlaceLevel _ _ Val c.i fuelR hfuel4 w.top.rootKey (X D)
          (X (D + 1)) w.next (w.next + 2) (Nn D) _ out.1 out.2.1 (K (D + 1)) r.1 j0
          hV hwfV hVq hrqV hqlf hqwf hqtimes hkl hqx hj0 (updN_self _ _ _)
          (hVfr w.next (Nat.le_refl _)) (hVfr (w.next + 2) (by omega))
          (fun u c' z hu hl => ⟨fun h => hVfresh w.next (Nat.le_refl _) u c'
              (reachS_tReach _ _ _ _ hu) (h ▸ hl),
            fun h => hVfresh (w.next + 2) (by omega) u c' (reachS_tReach _ _ _ _ hu) (h ▸ hl)⟩)
          hRn (by rw [hw']; simp only [↓reduceIte]) (by rw [hw']; simp only [hFj, hFq, ↓reduceIte])
          hhalf.1 hhalf.2.1 hhalf.2.2.1 hhalf.2.2.2.1 hhalf.2.2.2.2.1 hhalf.2.2.2.2.2
          (by rw [hw']; simp only [hqx, ↓reduceIte])
          (by
            intro z hz1 hz2 hz3 hz4
            rw [hw']
            simp only [hz1, hz2, hz3, hz4, ↓reduceIte]
            exact (updN_ne _ _ _ _ hz1).symm)
          (hvalx Val hVal _ (by omega)) (hrootN _ (by omega)) hrootX (hrootN _ (Nat.le_refl _))
          hdR key
      · have h := hNo.2 (by rw [hcf]; simpa using hsp)
        rw [hqlf] at h
        cases h
    · intro _ n hn cv y hk
      rw [hw'] at hn
      simp only [↓reduceIte, Option.some.injEq] at hn
      subst hn
      rw [← hout] at hk
      exact halves_nil_first_keys _ _ _ cv y hk
    · intro _ _ z hz hzx
      rw [h'top]
      exact hRB0 z hz (hzx _ (by omega) (Nat.le_refl _))
    · intro _ _
      rw [h'top]
      refine ⟨fun i h1 h2 => Or.inl ?_, fun z hz h => ?_⟩
      · rcases Nat.lt_or_ge i (D + 1) with hlt | hge
        · exact hRB0 _ (hanc _ i h1 (by omega))
            (fun he => by have := hdist _ _ h1 (by omega) (by omega) (Nat.le_refl _) he; omega)
        · have : i = D + 1 := by omega
          subst this
          exact hXr
      · rw [h'n] at h
        have h1' : ¬ z = X (D + 1) := by omega
        have h2' : ¬ z = X D := by omega
        by_cases h3' : z = w.next
        · subst h3'; exact hSr
        · by_cases h4' : z = w.next + 2
          · subst h4'; exact hRr
          · exfalso
            simp only [h1', h2', h3', h4', ↓reduceIte, (hS5 z hz).1, Option.isSome_none,
              Bool.false_eq_true] at h

  -- the dispatch: by the split's kind, the node's making and its parent's kind
  by_cases hsp : (!compact && decide (last.size > c.p.splitAbove)) = true
  · have hcf : compact = false := by
      cases compact with
      | false => rfl
      | true => simp at hsp
    have hsp' : c.p.splitAbove < last.size := by rw [hcf] at hsp; simpa using hsp
    subst hcf
    by_cases hmade : (Nn (D + 1)).firstTime = some c.i
    · cases hqlf : (Nn D).leaf
      · exact hSI hmade hqlf hsp'
      · exact hSSIP rfl hmade hqlf hsp'
    · cases hqlf : (Nn D).leaf
      · exact hstepS hmade hqlf hsp'
      · exact hSEG rfl hmade hqlf hsp'
  · have hcs : (!compact && decide (last.size > c.p.splitAbove)) = false := by simpa using hsp
    by_cases hmade : (Nn (D + 1)).firstTime = some c.i
    · exact hstepTI hmade hcs
    · exact hstepT hmade hcs

end SIS.Tree
