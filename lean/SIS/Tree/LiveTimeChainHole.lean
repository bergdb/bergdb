/-
The parent's split with the hole below it: the live counts (bergdb 030-01, R4's open part).
The merge's parent p (X (D + 1)), not made by the transaction, thin after the merge (its
last version with fewer than m live klongs: the hole), named by a segment leaf (a segment
root, as in l4f's 69 thin-copy cascades), splits in time; its copy y (the next id) is the
hole after, and the cascade above it is any (`writerWP_appendKlongs_chainGLX` with E the
copy, a node named by segment leaves only). `writerWP_handleFull_timeChainV_liveHole`:
l4f's `writerWP_handleFull_timeChainV_live` with the hole, from `LiveEdgesX` with E p on the
tree V with p's node its last version to `LiveEdgesX` with E y after.
-/
import SIS.Tree.LiveMergeTimeChain

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- `liveEdgesX_of_sim` with E1 before and E2 after. -/
theorem liveEdgesX_of_sim2 (p : Params) (E1 E2 : NodeId → Prop) (N1 N2 : NodeId → Option KNode) (t : Time)
    (r1 r2 : NodeId)
    (h : LiveEdgesX p N1 t r1 E1) (hroot : ∀ rn, N2 r2 = some rn → RootOK t rn)
    (hedge : ∀ u un c z zn, TReach N2 t r2 u → N2 u = some un → (c, z) ∈ un.liveAt t →
      N2 z = some zn → (¬ E2 z ∧ ChildOK p t un zn) ∨
      ∃ u0 un0 c0 z0 zn0, TReach N1 t r1 u0 ∧ N1 u0 = some un0 ∧ (c0, z0) ∈ un0.liveAt t ∧
        N1 z0 = some zn0 ∧ un0.leaf = un.leaf ∧ zn0.leaf = zn.leaf ∧
        (zn0.liveAt t).length ≤ (zn.liveAt t).length ∧ (E1 z0 ↔ E2 z)) :
    LiveEdgesX p N2 t r2 E2 := by
  refine ⟨hroot, fun u un c z zn hu hun hc hzn => ?_⟩
  rcases hedge u un c z zn hu hun hc hzn with ⟨hnE, hok⟩ |
    ⟨u0, un0, c0, z0, zn0, hu0, hun0, hc0, hz0, hl1, hl2, hlen, hEz0⟩
  · exact ⟨fun _ => hok, fun hE => absurd hE hnE⟩
  · have h0 := h.2 u0 un0 c0 z0 zn0 hu0 hun0 hc0 hz0
    refine ⟨fun hn => childOK_grow p t un0 un zn0 zn (h0.1 (fun hE => hn (hEz0.mp hE))) hl1.symm
      hl2.symm hlen, fun hE => ?_⟩
    rw [← hl1]; exact h0.2 (hEz0.mpr hE)

/-- `liveEdges_updN_unreach` for `LiveEdgesX`. -/
theorem liveEdgesX_updN_unreach (p : Params) (E : NodeId → Prop) (N : NodeId → Option KNode) (t : Time)
    (r x : NodeId) (m : KNode) (hx : ¬ TReach N t r x) (h : LiveEdgesX p N t r E) :
    LiveEdgesX p (updN N x m) t r E := by
  have hback := tReach_updN_unreach N t r x m hx
  refine ⟨fun rn hrn => ?_, fun u un c y yn hu hun hc hyn => ?_⟩
  · have hrx : r ≠ x := fun he => hx (by rw [← he]; exact TReach.root)
    rw [updN_ne _ _ _ _ hrx] at hrn; exact h.1 rn hrn
  · have hu' := hback u hu
    have hux : u ≠ x := fun he => hx (by rw [← he]; exact hu')
    rw [updN_ne _ _ _ _ hux] at hun
    have hyx : y ≠ x := fun he => hx (by rw [← he]; exact TReach.link hu' ⟨un, hun, hc⟩)
    rw [updN_ne _ _ _ _ hyx] at hyn
    exact h.2 u un c y yn hu' hun hc hyn

/-- `liveEdgesX_timeSplit_gen` with the hole moving: E1 before (L's node may be in it), E2
after, y in E2 as L in E1, the rest alike. -/
theorem liveEdgesX_timeSplit_hole (p : Params) (E1 E2 : NodeId → Prop) (N N' : NodeId → Option KNode) (t : Time) (r q L y : NodeId)
    (qn n m qn' : KNode) (k1 : Nat)
    (hT : TreeOK N t r) (hq : TReach N t r q) (hqn : N q = some qn) (hqk : (k1, L) ∈ qn.liveAt t)
    (hLn : N L = some n)
    (hN'q : N' q = some qn')
    (hq' : ∀ c z, (c, z) ∈ qn'.liveAt t → (c = k1 ∧ z = y) ∨ (c ≠ k1 ∧ (c, z) ∈ qn.liveAt t))
    (hN'y : N' y = some m)
    (hmsub : ∀ c z, (c, z) ∈ m.liveAt t → (c, z) ∈ n.liveAt t)
    (hother : ∀ z, z ≠ L → z ≠ q → z ≠ y → N' z = N z)
    (hfy : N y = none) (hfresh : ∀ u c', TReach N t r u → ¬ TLink N t u c' y)
    (hEyL : E1 L ↔ E2 y) (hEo : ∀ z, z ≠ y → z ≠ L → (E1 z ↔ E2 z))
    (hml : m.leaf = n.leaf) (hmlen : (n.liveAt t).length ≤ (m.liveAt t).length)
    (hq'l : qn'.leaf = qn.leaf) (hq'len : (qn.liveAt t).length ≤ (qn'.liveAt t).length)
    (h : LiveEdgesX p N t r E1) : LiveEdgesX p N' t r E2 := by
  obtain ⟨_, hR'⟩ := treeOK_timeSplit_gen N N' t r q L y qn n m qn' k1 hT hq hqn hqk hLn hN'q hq'
    hN'y hmsub hother hfy hfresh
  have hL : TReach N t r L := TReach.link hq ⟨qn, hqn, hqk⟩
  have hyR : ∀ v, TReach N t r v → v ≠ y := by
    intro v hv hvy
    subst hvy
    cases hv with
    | root => obtain ⟨mm, hm⟩ := hT.rootKey; rw [hm] at hfy; cases hfy
    | link hu hl => exact hfresh _ _ hu hl
  have hqy : q ≠ y := hyR q hq
  -- a node of the tree after, but y, as the same node before
  have hsame : ∀ z zn, N' z = some zn → TReach N' t r z → z ≠ y →
      ∃ zn0, N z = some zn0 ∧ TReach N t r z ∧ zn0.leaf = zn.leaf ∧
        (zn0.liveAt t).length ≤ (zn.liveAt t).length ∧
        ∀ c v, (c, v) ∈ zn.liveAt t → (∃ c', (c', v) ∈ zn0.liveAt t) ∨ v = y := by
    intro z zn hz hzR hzy
    obtain ⟨hzR', hzL⟩ := hR' z hzR
    have hzR0 : TReach N t r z := by
      rcases hzR' with h' | h'
      · exact h'
      · exact absurd h' hzy
    by_cases hzq : z = q
    · subst hzq
      rw [hN'q] at hz
      cases hz
      refine ⟨qn, hqn, hzR0, hq'l.symm, hq'len, fun c v hc => ?_⟩
      rcases hq' c v hc with ⟨_, hv⟩ | ⟨_, hc'⟩
      · exact Or.inr hv
      · exact Or.inl ⟨c, hc'⟩
    · rw [hother z hzL hzq hzy] at hz
      exact ⟨zn, hz, hzR0, rfl, Nat.le_refl _, fun c v hc => Or.inl ⟨c, hc⟩⟩
  refine liveEdgesX_of_sim2 p E1 E2 N N' t r r h ?_ ?_
  · intro rn hrn
    obtain ⟨rn0, hr0, _, hl, hlen, _⟩ := hsame r rn hrn TReach.root (hyR r TReach.root)
    exact rootOK_grow t rn0 rn (h.1 rn0 hr0) hl.symm hlen
  · intro u un c z zn hu hun hc hzn
    right
    -- the link before: from u (or L for y) to z (or L for y)
    have hsrc : ∃ u0 un0, N u0 = some un0 ∧ TReach N t r u0 ∧ un0.leaf = un.leaf ∧
        ∀ c v, (c, v) ∈ un.liveAt t → (∃ c', (c', v) ∈ un0.liveAt t) ∨ (v = y ∧ u0 = q ∧ c = k1) := by
      by_cases huy : u = y
      · subst huy
        rw [hN'y] at hun
        cases hun
        exact ⟨L, n, hLn, hL, hml.symm, fun c v hc => Or.inl ⟨c, hmsub c v hc⟩⟩
      · obtain ⟨un0, hu0, huR, hl, _, hch⟩ := hsame u un hun hu huy
        refine ⟨u, un0, hu0, huR, hl, fun c v hc => ?_⟩
        by_cases huq : u = q
        · subst huq
          rw [hN'q] at hun
          cases hun
          rcases hq' c v hc with ⟨hck, hv⟩ | ⟨_, hc'⟩
          · exact Or.inr ⟨hv, rfl, hck⟩
          · rw [hqn] at hu0; cases hu0; exact Or.inl ⟨c, hc'⟩
        · rcases hch c v hc with h' | h'
          · exact Or.inl h'
          · exfalso
            subst h'
            rw [hother u (fun h'' => by subst h''; exact (hR' _ hu).2 rfl) huq huy] at hun
            exact hfresh u c huR ⟨un, hun, hc⟩
    obtain ⟨u0, un0, hu0, huR, hul, hch⟩ := hsrc
    by_cases hzy : z = y
    · subst hzy
      rw [hN'y] at hzn
      cases hzn
      rcases hch c z hc with ⟨c', hc'⟩ | ⟨_, hu0q, _⟩
      · exact absurd (TReach.link huR ⟨un0, hu0, hc'⟩) (fun h' => hyR _ h' rfl)
      · subst hu0q
        rw [hqn] at hu0; cases hu0
        exact ⟨u0, qn, k1, L, n, huR, hqn, hqk, hLn, hul, hml.symm, hmlen,
          hEyL⟩
    · have hzR : TReach N' t r z := TReach.link hu ⟨un, hun, hc⟩
      obtain ⟨zn0, hz0, _, hzl, hzlen, _⟩ := hsame z zn hzn hzR hzy
      rcases hch c z hc with ⟨c', hc'⟩ | ⟨hzy', _, _⟩
      · exact ⟨u0, un0, c', z, zn0, huR, hu0, hc', hz0, hul, hzl, hzlen,
          hEo z hzy (hR' z hzR).2⟩
      · exact absurd hzy' hzy


set_option maxHeartbeats 8000000 in
/-- l4f's `writerWP_handleFull_timeChainV_live` with the hole: X (D + 1) thin in V
(`LiveEdgesX` with E it), its copy, the next id, thin after (E it), any cascade above. -/
theorem writerWP_handleFull_timeChainV_liveHole (c : Ctx) (base : View BVal)
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
    (hLV0 : LiveEdgesX c.p (updN (wNode c.p base w) (X (D + 1)) ⟨(Nn (D + 1)).leaf, last.ks⟩) c.i
      w.top.rootKey (fun z => z = X (D + 1))) :
    WriterWP (handleFullWith (fun q more => appendKlongs D q more) (D + 1) (X (D + 1)) [] last
      compact) c w (fun _ w' =>
        LiveEdgesX c.p (wNode c.p base w') c.i w'.top.rootKey (fun z => z = w.next) ∧
        w'.nodes.lookup w.next = some ⟨(Nn (D + 1)).leaf, last.ks⟩ ∧
        (∀ z, TReach (wNode c.p base w') c.i w'.top.rootKey z →
          (TReach (updN (wNode c.p base w) (X (D + 1)) ⟨(Nn (D + 1)).leaf, last.ks⟩) c.i w.top.rootKey z ∨ w.next ≤ z) ∧ z ≠ X (D + 1)) ∧
        w'.taken = w.taken) := by
  have hXlt0 : ∀ i, i ≤ D + 1 → X i < w.next := by
    intro i h2
    obtain ⟨hl, _⟩ := hS2 i h2
    rcases Nat.lt_or_ge (X i) w.next with hlt | hge
    · exact hlt
    · have := (hS5 (X i) hge).1
      rw [hl] at this; cases this
  have hchain := writerWP_appendKlongs_chainGLX c base path0 0 D X K Nn
    (fun i _ h2 => hX i (by omega)) (fun i h1 h2 => hK i h1 (by omega))
    (fun i h1 h2 => hlinkK i h1 (by omega)) hrange hlen
    (fun i _ h2 => hwf i (by omega)) (fun i _ h2 => htimes i (by omega)) (Or.inr rfl)
    (fun i i' _ h2 _ h4 => hdist i i' (by omega) (by omega)) (fun z => z = w.next)
    (fun i _ h2 he => by have := hXlt0 i (by omega); omega) D (by omega)
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
  have hLV := liveEdgesX_timeSplit_hole c.p (fun z => z = X (D + 1)) (fun z => z = w.next) (updN (wNode c.p base w) (X (D + 1))
      ⟨(Nn (D + 1)).leaf, last.ks⟩)
    (updN (wNode c.p base w1) (X D) ([(K (D + 1), w.next)].foldl
      (fun n (cv, y) => n.add c.i (.key cv y)) (Nn D))) c.i w.top.rootKey (X D) (X (D + 1)) w.next
    (Nn D) ⟨(Nn (D + 1)).leaf, last.ks⟩ ⟨(Nn (D + 1)).leaf, last.ks⟩
    ([(K (D + 1), w.next)].foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn D)) (K (D + 1))
    hTV hqV hqnV hkl (updN_self _ _ _) (updN_self _ _ _) hqlinks hN'y (fun _ _ h => h) hoth hfyV hfreshV
    (by simp) (fun z h1 h2 => by simp [h1, h2]) rfl (Nat.le_refl _) hq'l
    (addKeys_liveAt_length c.i [(K (D + 1), w.next)] (Nn D) hqwf hqtimes) hLV0
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
    (fun z hz => by rw [hz, h1next]; omega)
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
  have hy2 : w2.nodes.lookup w.next = some ⟨(Nn (D + 1)).leaf, last.ks⟩ := by
    rw [h2frame _ (by rw [h1next]; omega)
      (fun i _ h2 he => by have := hXlt i (by omega); omega)]
    rw [h1n]; exact lookup_append_single_self _ _ _ hfree0
  have key : ∀ w3 : W, w3.nodes = upsert w2.nodes (X (D + 1)) ((Nn (D + 1)).toPrev (c.i - 1)) →
      w3.taken = w2.taken → w3.top = w2.top →
      LiveEdgesX c.p (wNode c.p base w3) c.i w3.top.rootKey (fun z => z = w.next) ∧
      w3.nodes.lookup w.next = some ⟨(Nn (D + 1)).leaf, last.ks⟩ ∧
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
    have hLV' := hLV
    rw [← h1top] at hLV'
    refine ⟨?_, ?_, ?_, by rw [h3t, h2t, h1t]⟩
    · rw [hN3, h3top]
      exact liveEdgesX_updN_unreach _ _ _ _ _ _ _ hxR2 (h2live hmp hLV')
    · rw [h3n, lookup_upsert]
      simp only [Ne.symm hXn1, ↓reduceIte]
      exact hy2
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



/-- The merge's form of the hole (`LiveEdgesH` with the hole L) as `LiveEdgesX` with E L,
when every reached namer of L is a segment leaf and L is not the space root. -/
theorem liveEdgesX_of_holeH (p : Params) (N : NodeId → Option KNode) (t : Time) (r L : NodeId)
    (h : LiveEdgesH p N t r (fun z => z = L)) (hrL : r ≠ L)
    (hpar : ∀ u un c, TReach N t r u → N u = some un → (c, L) ∈ un.liveAt t → un.leaf = true) :
    LiveEdgesX p N t r (fun z => z = L) :=
  ⟨fun rn hrn => ⟨(h.1 rn hrn).1, (h.1 rn hrn).2 hrL⟩,
    fun u un c y yn hu hun hc hyn => ⟨fun hy => (h.2 u un c y yn hu hun hc hyn).1 hy,
      fun hy => by subst hy; exact hpar u un c hu hun hc⟩⟩

/-- `LiveEdgesX` with E y as the hole's form, when y's node keeps a live klong. -/
theorem liveEdgesH_of_holeX (p : Params) (N : NodeId → Option KNode) (t : Time) (r y : NodeId)
    (h : LiveEdgesX p N t r (fun z => z = y)) (hy : ∀ yn, N y = some yn → yn.liveAt t ≠ []) :
    LiveEdgesH p N t r (fun z => z = y) :=
  ⟨fun rn hrn => ⟨(h.1 rn hrn).1, fun _ => (h.1 rn hrn).2⟩,
    fun u un c z zn hu hun hc hzn => ⟨fun hz => (h.2 u un c z zn hu hun hc hzn).1 hz,
      fun hz => by subst hz; exact hy zn hzn⟩⟩

end SIS.Tree
