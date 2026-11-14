/-
The steps of a cascade of splits for `LiveEdges` (bergdb 024-12, TP7, toward
`QLive` of the put into a full leaf): each takes the hypotheses of the matching
step of the writer's tree (`treeOK_timeSplit_gen`, `treeOK_spaceSplit_gen`,
`treeOK_spaceInPlaceStep` and the others), uses its reach, and adds what the
counts need: the kinds kept, no live klong lost, and a space split's halves
with the counts of `HalfOK` (`halves_lastVersionGivenDel_live_fill`).

`liveEdges_of_sim` is the common step: every link of the tree after keeps
`ChildOK` directly, or stands for a link of the tree before whose ends have
the same kinds, the node named having no fewer live klongs after.
-/
import SIS.Tree.LiveEdges
import SIS.Tree.WriterTreeChainTree

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- The common step: every link of N2's tree keeps `ChildOK` directly or stands
for a link of N1's tree with the same kinds at its ends and no more live
klongs at its end; N2's root keeps `RootOK`. -/
theorem liveEdges_of_sim (p : Params) (N1 N2 : NodeId → Option KNode) (t : Time) (r1 r2 : NodeId)
    (h : LiveEdges p N1 t r1) (hroot : ∀ rn, N2 r2 = some rn → RootOK t rn)
    (hedge : ∀ u un c z zn, TReach N2 t r2 u → N2 u = some un → (c, z) ∈ un.liveAt t →
      N2 z = some zn → ChildOK p t un zn ∨
      ∃ u0 un0 c0 z0 zn0, TReach N1 t r1 u0 ∧ N1 u0 = some un0 ∧ (c0, z0) ∈ un0.liveAt t ∧
        N1 z0 = some zn0 ∧ un0.leaf = un.leaf ∧ zn0.leaf = zn.leaf ∧
        (zn0.liveAt t).length ≤ (zn.liveAt t).length) :
    LiveEdges p N2 t r2 := by
  refine ⟨hroot, fun u un c z zn hu hun hc hzn => ?_⟩
  rcases hedge u un c z zn hu hun hc hzn with hok | ⟨u0, un0, c0, z0, zn0, hu0, hun0, hc0, hz0, hl1, hl2, hlen⟩
  · exact hok
  · exact childOK_grow p t un0 un zn0 zn (h.2 u0 un0 c0 z0 zn0 hu0 hun0 hc0 hz0) hl1.symm hl2.symm hlen

theorem rootOK_grow (t : Time) (rn rn' : KNode) (h : RootOK t rn) (hl : rn'.leaf = rn.leaf)
    (hlen : (rn.liveAt t).length ≤ (rn'.liveAt t).length) : RootOK t rn' := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun hE => ?_, fun hl' => ?_⟩
  · have h0 : (rn'.liveAt t).length = 0 := by rw [hE]; rfl
    rw [hl]; exact h1 (List.eq_nil_of_length_eq_zero (by omega))
  · rw [hl] at hl'; have := h2 hl'; omega

/-! ## A time split to a new node below q -/

/-- `treeOK_timeSplit_gen` for `LiveEdges`: L's last version y (L's kind, no
fewer live klongs, live pointees of L's), q's klong k1 to y (q's kind, no fewer
live klongs). -/
theorem liveEdges_timeSplit_gen (p : Params) (N N' : NodeId → Option KNode) (t : Time) (r q L y : NodeId)
    (qn n m qn' : KNode) (k1 : Nat)
    (hT : TreeOK N t r) (hq : TReach N t r q) (hqn : N q = some qn) (hqk : (k1, L) ∈ qn.liveAt t)
    (hLn : N L = some n)
    (hN'q : N' q = some qn')
    (hq' : ∀ c z, (c, z) ∈ qn'.liveAt t → (c = k1 ∧ z = y) ∨ (c ≠ k1 ∧ (c, z) ∈ qn.liveAt t))
    (hN'y : N' y = some m)
    (hmsub : ∀ c z, (c, z) ∈ m.liveAt t → (c, z) ∈ n.liveAt t)
    (hother : ∀ z, z ≠ L → z ≠ q → z ≠ y → N' z = N z)
    (hfy : N y = none) (hfresh : ∀ u c', TReach N t r u → ¬ TLink N t u c' y)
    (hml : m.leaf = n.leaf) (hmlen : (n.liveAt t).length ≤ (m.liveAt t).length)
    (hq'l : qn'.leaf = qn.leaf) (hq'len : (qn.liveAt t).length ≤ (qn'.liveAt t).length)
    (h : LiveEdges p N t r) : LiveEdges p N' t r := by
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
  refine liveEdges_of_sim p N N' t r r h ?_ ?_
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
        exact ⟨u0, qn, k1, L, n, huR, hqn, hqk, hLn, hul, hml.symm, hmlen⟩
    · have hzR : TReach N' t r z := TReach.link hu ⟨un, hun, hc⟩
      obtain ⟨zn0, hz0, _, hzl, hzlen, _⟩ := hsame z zn hzn hzR hzy
      rcases hch c z hc with ⟨c', hc'⟩ | ⟨hzy', _, _⟩
      · exact ⟨u0, un0, c', z, zn0, huR, hu0, hc', hz0, hul, hzl, hzlen⟩
      · exact absurd hzy' hzy

/-! ## A space split to two new nodes below an inner q -/

/-- `treeOK_spaceSplit_gen` for `LiveEdges`: L's halves y1, y2 with L's kind,
live pointees of L's and the counts of `HalfOK`; q's klongs to them (q's kind, no
fewer live klongs). -/
theorem liveEdges_spaceSplit_gen (p : Params) (N N' : NodeId → Option KNode) (t : Time)
    (r q L y1 y2 : NodeId) (qn n f s qn' : KNode) (k1 sc : Nat) (loc : Nat → Nat)
    (hT : TreeOK N t r) (hq : TReach N t r q) (hqn : N q = some qn) (hqk : (k1, L) ∈ qn.liveAt t)
    (hLn : N L = some n)
    (hN'q : N' q = some qn')
    (hq' : ∀ c z, (c, z) ∈ qn'.liveAt t → (c = sc ∧ z = y2) ∨ (c ≠ sc ∧ c = k1 ∧ z = y1) ∨
      (c ≠ sc ∧ c ≠ k1 ∧ (c, z) ∈ qn.liveAt t))
    (hN'1 : N' y1 = some f) (hN'2 : N' y2 = some s)
    (hf : ∀ c z, (c, z) ∈ f.liveAt t → c < sc ∧ (c, z) ∈ n.liveAt t)
    (hs : ∀ c z, (c, z) ∈ s.liveAt t → ∃ c0, sc ≤ c0 ∧ c = loc c0 ∧ (c0, z) ∈ n.liveAt t)
    (hother : ∀ z, z ≠ L → z ≠ q → z ≠ y1 → z ≠ y2 → N' z = N z)
    (hf1 : N y1 = none) (hf2 : N y2 = none) (h12 : y1 ≠ y2)
    (hfresh : ∀ z, (z = y1 ∨ z = y2) → ∀ u c', TReach N t r u → ¬ TLink N t u c' z)
    (hfl : f.leaf = n.leaf) (hsl : s.leaf = n.leaf) (hfH : HalfOK p t f) (hsH : HalfOK p t s)
    (hq'l : qn'.leaf = qn.leaf) (hq'len : (qn.liveAt t).length ≤ (qn'.liveAt t).length)
    (h : LiveEdges p N t r) : LiveEdges p N' t r := by
  obtain ⟨_, hR'⟩ := treeOK_spaceSplit_gen N N' t r q L y1 y2 qn n f s qn' k1 sc loc hT hq hqn hqk
    hLn hN'q hq' hN'1 hN'2 hf hs hother hf1 hf2 h12 hfresh
  have hL : TReach N t r L := TReach.link hq ⟨qn, hqn, hqk⟩
  have hnew : ∀ v, TReach N t r v → v ≠ y1 ∧ v ≠ y2 := by
    intro v hv
    constructor
    · intro hvy; subst hvy
      cases hv with
      | root => obtain ⟨mm, hm⟩ := hT.rootKey; rw [hm] at hf1; cases hf1
      | link hu hl => exact hfresh _ (Or.inl rfl) _ _ hu hl
    · intro hvy; subst hvy
      cases hv with
      | root => obtain ⟨mm, hm⟩ := hT.rootKey; rw [hm] at hf2; cases hf2
      | link hu hl => exact hfresh _ (Or.inr rfl) _ _ hu hl
  have hsame : ∀ z zn, N' z = some zn → TReach N' t r z → z ≠ y1 → z ≠ y2 →
      ∃ zn0, N z = some zn0 ∧ TReach N t r z ∧ zn0.leaf = zn.leaf ∧
        (zn0.liveAt t).length ≤ (zn.liveAt t).length ∧
        ∀ c v, (c, v) ∈ zn.liveAt t → (∃ c', (c', v) ∈ zn0.liveAt t) ∨ v = y1 ∨ v = y2 := by
    intro z zn hz hzR hz1 hz2
    obtain ⟨hzR', hzL⟩ := hR' z hzR
    have hzR0 : TReach N t r z := by
      rcases hzR' with h' | h' | h'
      · exact h'
      · exact absurd h' hz1
      · exact absurd h' hz2
    by_cases hzq : z = q
    · subst hzq
      rw [hN'q] at hz
      cases hz
      refine ⟨qn, hqn, hzR0, hq'l.symm, hq'len, fun c v hc => ?_⟩
      rcases hq' c v hc with ⟨_, hv⟩ | ⟨_, _, hv⟩ | ⟨_, _, hc'⟩
      · exact Or.inr (Or.inr hv)
      · exact Or.inr (Or.inl hv)
      · exact Or.inl ⟨c, hc'⟩
    · rw [hother z hzL hzq hz1 hz2] at hz
      exact ⟨zn, hz, hzR0, rfl, Nat.le_refl _, fun c v hc => Or.inl ⟨c, hc⟩⟩
  refine liveEdges_of_sim p N N' t r r h ?_ ?_
  · intro rn hrn
    obtain ⟨hr1, hr2⟩ := hnew r TReach.root
    obtain ⟨rn0, hr0, _, hl, hlen, _⟩ := hsame r rn hrn TReach.root hr1 hr2
    exact rootOK_grow t rn0 rn (h.1 rn0 hr0) hl.symm hlen
  · intro u un c z zn hu hun hc hzn
    by_cases hz1 : z = y1
    · subst hz1; rw [hN'1] at hzn; cases hzn; exact Or.inl (childOK_half p t un f hfH)
    by_cases hz2 : z = y2
    · subst hz2; rw [hN'2] at hzn; cases hzn; exact Or.inl (childOK_half p t un s hsH)
    right
    have hsrc : ∃ u0 un0, N u0 = some un0 ∧ TReach N t r u0 ∧ un0.leaf = un.leaf ∧
        ∀ c v, (c, v) ∈ un.liveAt t → (∃ c', (c', v) ∈ un0.liveAt t) ∨ v = y1 ∨ v = y2 := by
      by_cases hu1 : u = y1
      · subst hu1
        rw [hN'1] at hun
        cases hun
        exact ⟨L, n, hLn, hL, hfl.symm, fun c v hc => Or.inl ⟨c, (hf c v hc).2⟩⟩
      by_cases hu2 : u = y2
      · subst hu2
        rw [hN'2] at hun
        cases hun
        refine ⟨L, n, hLn, hL, hsl.symm, fun c v hc => ?_⟩
        obtain ⟨c0, _, _, hc0⟩ := hs c v hc
        exact Or.inl ⟨c0, hc0⟩
      obtain ⟨un0, hu0, huR, hl, _, hch⟩ := hsame u un hun hu hu1 hu2
      exact ⟨u, un0, hu0, huR, hl, hch⟩
    obtain ⟨u0, un0, hu0, huR, hul, hch⟩ := hsrc
    have hzR : TReach N' t r z := TReach.link hu ⟨un, hun, hc⟩
    obtain ⟨zn0, hz0, _, hzl, hzlen, _⟩ := hsame z zn hzn hzR hz1 hz2
    rcases hch c z hc with ⟨c', hc'⟩ | hzy | hzy
    · exact ⟨u0, un0, c', z, zn0, huR, hu0, hc', hz0, hul, hzl, hzlen⟩
    · exact absurd hzy hz1
    · exact absurd hzy hz2

/-! ## A time split in place -/

theorem updN_updN_same (N : NodeId → Option KNode) (x : NodeId) (m m' : KNode) :
    updN (updN N x m) x m' = updN N x m' := by
  funext z
  by_cases hz : z = x
  · subst hz; rw [updN_self, updN_self]
  · rw [updN_ne _ _ _ _ hz, updN_ne _ _ _ _ hz, updN_ne _ _ _ _ hz]

/-- `treeOK_updN_sub` for `LiveEdges`: x's klongs replaced by ones of its kind
with live pointees of its, no fewer live klongs. -/
theorem liveEdges_updN_sub (p : Params) (N : NodeId → Option KNode) (t : Time) (r x : NodeId)
    (m m' : KNode) (hsub : ∀ c z, (c, z) ∈ m'.liveAt t → (c, z) ∈ m.liveAt t)
    (hl : m'.leaf = m.leaf) (hlen : (m.liveAt t).length ≤ (m'.liveAt t).length)
    (h : LiveEdges p (updN N x m) t r) : LiveEdges p (updN N x m') t r := by
  have := liveEdges_updN_grow p (updN N x m) t r x m m' (updN_self _ _ _) hl
    (fun c z hc => Or.inl ⟨c, hsub c z hc⟩) hlen h
  rwa [updN_updN_same] at this

/-! ## The space splits in place and below a segment leaf -/

/-- `treeOK_spaceInPlaceStep` for `LiveEdges`: x keeps its first half f, the new
S the second s, both of x's kind with x's live pointees and the counts of
`HalfOK`; q gets S (its kind, no fewer live klongs). -/
theorem liveEdges_spaceInPlaceStep (p : Params) (N1 N2 : NodeId → Option KNode) (t : Time)
    (r q x S : NodeId) (qn vx f s qn' : KNode) (k1 sc : Nat) (loc : Nat → Nat)
    (hT : TreeOK N1 t r) (hq : TReach N1 t r q) (hqn : N1 q = some qn) (hqk : (k1, x) ∈ qn.liveAt t)
    (hxn : N1 x = some vx)
    (hN2q : N2 q = some qn')
    (hq' : ∀ c z, (c, z) ∈ qn'.liveAt t → (c = sc ∧ z = S) ∨ (c ≠ sc ∧ (c, z) ∈ qn.liveAt t))
    (hN2x : N2 x = some f) (hN2S : N2 S = some s)
    (hf : ∀ c z, (c, z) ∈ f.liveAt t → c < sc ∧ (c, z) ∈ vx.liveAt t)
    (hs : ∀ c z, (c, z) ∈ s.liveAt t → ∃ c0, sc ≤ c0 ∧ c = loc c0 ∧ (c0, z) ∈ vx.liveAt t)
    (hother : ∀ z, z ≠ x → z ≠ q → z ≠ S → N2 z = N1 z)
    (hfS : N1 S = none) (hfresh : ∀ u c', TReach N1 t r u → ¬ TLink N1 t u c' S)
    (hfl : f.leaf = vx.leaf) (hsl : s.leaf = vx.leaf) (hfH : HalfOK p t f) (hsH : HalfOK p t s)
    (hq'l : qn'.leaf = qn.leaf) (hq'len : (qn.liveAt t).length ≤ (qn'.liveAt t).length)
    (h : LiveEdges p N1 t r) : LiveEdges p N2 t r := by
  obtain ⟨_, hR'⟩ := treeOK_spaceInPlaceStep N1 N2 t r q x S qn vx f s qn' k1 sc loc hT hq hqn hqk
    hxn hN2q hq' hN2x hN2S hf hs hother hfS hfresh
  have hx : TReach N1 t r x := TReach.link hq ⟨qn, hqn, hqk⟩
  have hSn : ∀ v, TReach N1 t r v → v ≠ S := by
    intro v hv hvS; subst hvS
    cases hv with
    | root => obtain ⟨mm, hm⟩ := hT.rootKey; rw [hm] at hfS; cases hfS
    | link hu hl => exact hfresh _ _ hu hl
  have hsame : ∀ z zn, N2 z = some zn → TReach N2 t r z → z ≠ x → z ≠ S →
      ∃ zn0, N1 z = some zn0 ∧ TReach N1 t r z ∧ zn0.leaf = zn.leaf ∧
        (zn0.liveAt t).length ≤ (zn.liveAt t).length ∧
        ∀ c v, (c, v) ∈ zn.liveAt t → (∃ c', (c', v) ∈ zn0.liveAt t) ∨ v = S := by
    intro z zn hz hzR hzx hzS
    have hzR0 : TReach N1 t r z := by
      rcases hR' z hzR with h' | h'
      · exact h'
      · exact absurd h' hzS
    by_cases hzq : z = q
    · subst hzq
      rw [hN2q] at hz
      cases hz
      refine ⟨qn, hqn, hzR0, hq'l.symm, hq'len, fun c v hc => ?_⟩
      rcases hq' c v hc with ⟨_, hv⟩ | ⟨_, hc'⟩
      · exact Or.inr hv
      · exact Or.inl ⟨c, hc'⟩
    · rw [hother z hzx hzq hzS] at hz
      exact ⟨zn, hz, hzR0, rfl, Nat.le_refl _, fun c v hc => Or.inl ⟨c, hc⟩⟩
  refine liveEdges_of_sim p N1 N2 t r r h ?_ ?_
  · intro rn hrn
    by_cases hrx : r = x
    · rw [hrx, hN2x] at hrn; cases hrn; exact rootOK_half p t f hfH
    obtain ⟨rn0, hr0, _, hl, hlen, _⟩ := hsame r rn hrn TReach.root hrx (hSn r TReach.root)
    exact rootOK_grow t rn0 rn (h.1 rn0 hr0) hl.symm hlen
  · intro u un c z zn hu hun hc hzn
    by_cases hzx : z = x
    · subst hzx; rw [hN2x] at hzn; cases hzn; exact Or.inl (childOK_half p t un f hfH)
    by_cases hzS : z = S
    · subst hzS; rw [hN2S] at hzn; cases hzn; exact Or.inl (childOK_half p t un s hsH)
    right
    have hsrc : ∃ u0 un0, N1 u0 = some un0 ∧ TReach N1 t r u0 ∧ un0.leaf = un.leaf ∧
        ∀ c v, (c, v) ∈ un.liveAt t → (∃ c', (c', v) ∈ un0.liveAt t) ∨ v = S := by
      by_cases hux : u = x
      · subst hux
        rw [hN2x] at hun
        cases hun
        exact ⟨u, vx, hxn, hx, hfl.symm, fun c v hc => Or.inl ⟨c, (hf c v hc).2⟩⟩
      by_cases huS : u = S
      · subst huS
        rw [hN2S] at hun
        cases hun
        refine ⟨x, vx, hxn, hx, hsl.symm, fun c v hc => ?_⟩
        obtain ⟨c0, _, _, hc0⟩ := hs c v hc
        exact Or.inl ⟨c0, hc0⟩
      obtain ⟨un0, hu0, huR, hl, _, hch⟩ := hsame u un hun hu hux huS
      exact ⟨u, un0, hu0, huR, hl, hch⟩
    obtain ⟨u0, un0, hu0, huR, hul, hch⟩ := hsrc
    have hzR : TReach N2 t r z := TReach.link hu ⟨un, hun, hc⟩
    obtain ⟨zn0, hz0, _, hzl, hzlen, _⟩ := hsame z zn hzn hzR hzx hzS
    rcases hch c z hc with ⟨c', hc'⟩ | hzy
    · exact ⟨u0, un0, c', z, zn0, huR, hu0, hc', hz0, hul, hzl, hzlen⟩
    · exact absurd hzy hzS

/-- A node named by a segment leaf and holding two live klongs or more may be an
inner segment root. -/
theorem childOK_segRoot (p : Params) (t : Time) (un rn : KNode) (hul : un.leaf = true)
    (hrn2 : 2 ≤ (rn.liveAt t).length) : ChildOK p t un rn := by
  refine ⟨fun hE => ?_, fun _ _ => hrn2, fun hl _ => ?_⟩
  · rw [hE] at hrn2; simp at hrn2
  · rw [hul] at hl; cases hl

theorem rootOK_two (t : Time) (rn : KNode) (hrn2 : 2 ≤ (rn.liveAt t).length) : RootOK t rn := by
  refine ⟨fun hE => ?_, fun _ => hrn2⟩
  rw [hE] at hrn2; simp at hrn2

/-- `treeOK_segSpaceStep` for `LiveEdges`: the halves F, S (x's kind, x's live
pointees, `HalfOK`) under a new inner segment root R with two live klongs or
more, which the segment leaf q names (q's kind, no fewer live klongs). -/
theorem liveEdges_segSpaceStep (p : Params) (N1 N2 : NodeId → Option KNode) (t : Time)
    (r q x F S R : NodeId) (qn vx f s rn qn2 : KNode) (k1 sc : Nat) (loc : Nat → Nat) (hsc : 0 < sc)
    (hT : TreeOK N1 t r) (hq : TReach N1 t r q) (hqn : N1 q = some qn) (hqk : (k1, x) ∈ qn.liveAt t)
    (hxn : N1 x = some vx)
    (hN2q : N2 q = some qn2) (hq2k : (k1, R) ∈ qn2.liveAt t)
    (hq2 : ∀ c z, (c, z) ∈ qn2.liveAt t → (c = k1 ∧ z = R) ∨ (c ≠ k1 ∧ (c, z) ∈ qn.liveAt t))
    (hN2R : N2 R = some rn) (hrn : ∀ c z, (c, z) ∈ rn.liveAt t → (c = 0 ∧ z = F) ∨ (c = sc ∧ z = S))
    (hN2F : N2 F = some f) (hN2S : N2 S = some s)
    (hf : ∀ c z, (c, z) ∈ f.liveAt t → c < sc ∧ (c, z) ∈ vx.liveAt t)
    (hs : ∀ c z, (c, z) ∈ s.liveAt t → ∃ c0, sc ≤ c0 ∧ c = loc c0 ∧ (c0, z) ∈ vx.liveAt t)
    (hother : ∀ z, z ≠ x → z ≠ q → z ≠ F → z ≠ S → z ≠ R → N2 z = N1 z)
    (hfresh : ∀ z, (z = F ∨ z = S ∨ z = R) → N1 z = none ∧ ∀ u c', TReach N1 t r u → ¬ TLink N1 t u c' z)
    (hFS : F ≠ S) (hFR : F ≠ R) (hSR : S ≠ R)
    (hfl : f.leaf = vx.leaf) (hsl : s.leaf = vx.leaf) (hfH : HalfOK p t f) (hsH : HalfOK p t s)
    (hrn2 : 2 ≤ (rn.liveAt t).length) (hql : qn2.leaf = true) (hq2l : qn2.leaf = qn.leaf)
    (hq2len : (qn.liveAt t).length ≤ (qn2.liveAt t).length)
    (h : LiveEdges p N1 t r) : LiveEdges p N2 t r := by
  obtain ⟨_, hR'⟩ := treeOK_segSpaceStep N1 N2 t r q x F S R qn vx f s rn qn2 k1 sc loc hsc hT hq
    hqn hqk hxn hN2q hq2k hq2 hN2R hrn hN2F hN2S hf hs hother hfresh hFS hFR hSR
  have hx : TReach N1 t r x := TReach.link hq ⟨qn, hqn, hqk⟩
  have hnew : ∀ v, TReach N1 t r v → v ≠ F ∧ v ≠ S ∧ v ≠ R := by
    have hone : ∀ z, (z = F ∨ z = S ∨ z = R) → ∀ v, TReach N1 t r v → v ≠ z := by
      intro z hz v hv hvz; subst hvz
      obtain ⟨hn, hfr⟩ := hfresh v hz
      cases hv with
      | root => obtain ⟨mm, hm⟩ := hT.rootKey; rw [hm] at hn; cases hn
      | link hu hl => exact hfr _ _ hu hl
    intro v hv
    exact ⟨hone F (Or.inl rfl) v hv, hone S (Or.inr (Or.inl rfl)) v hv, hone R (Or.inr (Or.inr rfl)) v hv⟩
  have hsame : ∀ z zn, N2 z = some zn → TReach N2 t r z → z ≠ F → z ≠ S → z ≠ R →
      ∃ zn0, N1 z = some zn0 ∧ TReach N1 t r z ∧ zn0.leaf = zn.leaf ∧
        (zn0.liveAt t).length ≤ (zn.liveAt t).length ∧
        ∀ c v, (c, v) ∈ zn.liveAt t → (∃ c', (c', v) ∈ zn0.liveAt t) ∨ v = R := by
    intro z zn hz hzR hzF hzS hzRR
    obtain ⟨hzR', hzx⟩ := hR' z hzR
    have hzR0 : TReach N1 t r z := by
      rcases hzR' with h' | h' | h' | h'
      · exact h'
      · exact absurd h' hzF
      · exact absurd h' hzS
      · exact absurd h' hzRR
    by_cases hzq : z = q
    · subst hzq
      rw [hN2q] at hz
      cases hz
      refine ⟨qn, hqn, hzR0, hq2l.symm, hq2len, fun c v hc => ?_⟩
      rcases hq2 c v hc with ⟨_, hv⟩ | ⟨_, hc'⟩
      · exact Or.inr hv
      · exact Or.inl ⟨c, hc'⟩
    · rw [hother z hzx hzq hzF hzS hzRR] at hz
      exact ⟨zn, hz, hzR0, rfl, Nat.le_refl _, fun c v hc => Or.inl ⟨c, hc⟩⟩
  refine liveEdges_of_sim p N1 N2 t r r h ?_ ?_
  · intro rn' hrn'
    obtain ⟨hr1, hr2, hr3⟩ := hnew r TReach.root
    obtain ⟨rn0, hr0, _, hl, hlen, _⟩ := hsame r rn' hrn' TReach.root hr1 hr2 hr3
    exact rootOK_grow t rn0 rn' (h.1 rn0 hr0) hl.symm hlen
  · intro u un c z zn hu hun hc hzn
    by_cases hzF : z = F
    · subst hzF; rw [hN2F] at hzn; cases hzn; exact Or.inl (childOK_half p t un f hfH)
    by_cases hzS : z = S
    · subst hzS; rw [hN2S] at hzn; cases hzn; exact Or.inl (childOK_half p t un s hsH)
    -- the source of u: its node before, or x for a half; R names only the halves
    have hsrc : u ≠ R → ∃ u0 un0, N1 u0 = some un0 ∧ TReach N1 t r u0 ∧ un0.leaf = un.leaf ∧
        ∀ c v, (c, v) ∈ un.liveAt t → (∃ c', (c', v) ∈ un0.liveAt t) ∨ (v = R ∧ u = q) := by
      intro huR
      by_cases huF : u = F
      · subst huF
        rw [hN2F] at hun
        cases hun
        exact ⟨x, vx, hxn, hx, hfl.symm, fun c v hc => Or.inl ⟨c, (hf c v hc).2⟩⟩
      by_cases huS : u = S
      · subst huS
        rw [hN2S] at hun
        cases hun
        refine ⟨x, vx, hxn, hx, hsl.symm, fun c v hc => ?_⟩
        obtain ⟨c0, _, _, hc0⟩ := hs c v hc
        exact Or.inl ⟨c0, hc0⟩
      obtain ⟨un0, hu0, huR0, hl, _, hch⟩ := hsame u un hun hu huF huS huR
      refine ⟨u, un0, hu0, huR0, hl, fun c v hc => ?_⟩
      rcases hch c v hc with h' | hvR
      · exact Or.inl h'
      · by_cases huq : u = q
        · exact Or.inr ⟨hvR, huq⟩
        · exfalso
          subst hvR
          rw [hother u (hR' u hu).2 huq huF huS huR] at hun
          exact (hfresh v (Or.inr (Or.inr rfl))).2 u c huR0 ⟨un, hun, hc⟩
    by_cases huR : u = R
    · subst huR
      rw [hN2R] at hun
      cases hun
      rcases hrn c z hc with ⟨_, hz⟩ | ⟨_, hz⟩
      · exact absurd hz hzF
      · exact absurd hz hzS
    obtain ⟨u0, un0, hu0, huR0, hul, hch⟩ := hsrc huR
    by_cases hzR : z = R
    · subst hzR
      rw [hN2R] at hzn
      cases hzn
      rcases hch c z hc with ⟨c', hc'⟩ | ⟨_, huq⟩
      · exact absurd (TReach.link huR0 ⟨un0, hu0, hc'⟩) (fun h' => (hnew _ h').2.2 rfl)
      · subst huq
        rw [hN2q] at hun
        cases hun
        exact Or.inl (childOK_segRoot p t qn2 rn hql hrn2)
    right
    have hzR2 : TReach N2 t r z := TReach.link hu ⟨un, hun, hc⟩
    obtain ⟨zn0, hz0, _, hzl, hzlen, _⟩ := hsame z zn hzn hzR2 hzF hzS hzR
    rcases hch c z hc with ⟨c', hc'⟩ | ⟨hzy, _⟩
    · exact ⟨u0, un0, c', z, zn0, huR0, hu0, hc', hz0, hul, hzl, hzlen⟩
    · exact absurd hzy hzR

/-- `treeOK_segSpaceInPlaceStep` for `LiveEdges`: x keeps its first half f, the
new S the second (both `HalfOK`, x's kind, x's live pointees), under a new
inner segment root R with two live klongs or more, which the segment leaf q
names (q's kind, no fewer live klongs). -/
theorem liveEdges_segSpaceInPlaceStep (p : Params) (N1 N2 : NodeId → Option KNode) (t : Time)
    (r q x S R : NodeId) (qn vx f s rn qn2 : KNode) (k1 sc : Nat) (loc : Nat → Nat) (hsc : 0 < sc)
    (hT : TreeOK N1 t r) (hq : TReach N1 t r q) (hqn : N1 q = some qn) (hqk : (k1, x) ∈ qn.liveAt t)
    (hxn : N1 x = some vx)
    (hN2q : N2 q = some qn2) (hq2k : (k1, R) ∈ qn2.liveAt t)
    (hq2 : ∀ c z, (c, z) ∈ qn2.liveAt t → (c = k1 ∧ z = R) ∨ (c ≠ k1 ∧ (c, z) ∈ qn.liveAt t))
    (hN2R : N2 R = some rn) (hrn : ∀ c z, (c, z) ∈ rn.liveAt t → (c = 0 ∧ z = x) ∨ (c = sc ∧ z = S))
    (hN2x : N2 x = some f) (hN2S : N2 S = some s)
    (hf : ∀ c z, (c, z) ∈ f.liveAt t → c < sc ∧ (c, z) ∈ vx.liveAt t)
    (hs : ∀ c z, (c, z) ∈ s.liveAt t → ∃ c0, sc ≤ c0 ∧ c = loc c0 ∧ (c0, z) ∈ vx.liveAt t)
    (hother : ∀ z, z ≠ x → z ≠ q → z ≠ S → z ≠ R → N2 z = N1 z)
    (hfresh : ∀ z, (z = S ∨ z = R) → N1 z = none ∧ ∀ u c', TReach N1 t r u → ¬ TLink N1 t u c' z)
    (hSR : S ≠ R)
    (hfl : f.leaf = vx.leaf) (hsl : s.leaf = vx.leaf) (hfH : HalfOK p t f) (hsH : HalfOK p t s)
    (hrn2 : 2 ≤ (rn.liveAt t).length) (hql : qn2.leaf = true) (hq2l : qn2.leaf = qn.leaf)
    (hq2len : (qn.liveAt t).length ≤ (qn2.liveAt t).length)
    (h : LiveEdges p N1 t r) : LiveEdges p N2 t r := by
  obtain ⟨_, hR'⟩ := treeOK_segSpaceInPlaceStep N1 N2 t r q x S R qn vx f s rn qn2 k1 sc loc hsc hT
    hq hqn hqk hxn hN2q hq2k hq2 hN2R hrn hN2x hN2S hf hs hother hfresh hSR
  have hx : TReach N1 t r x := TReach.link hq ⟨qn, hqn, hqk⟩
  have hnew : ∀ v, TReach N1 t r v → v ≠ S ∧ v ≠ R := by
    have hone : ∀ z, (z = S ∨ z = R) → ∀ v, TReach N1 t r v → v ≠ z := by
      intro z hz v hv hvz; subst hvz
      obtain ⟨hn, hfr⟩ := hfresh v hz
      cases hv with
      | root => obtain ⟨mm, hm⟩ := hT.rootKey; rw [hm] at hn; cases hn
      | link hu hl => exact hfr _ _ hu hl
    intro v hv
    exact ⟨hone S (Or.inl rfl) v hv, hone R (Or.inr rfl) v hv⟩
  have hsame : ∀ z zn, N2 z = some zn → TReach N2 t r z → z ≠ x → z ≠ S → z ≠ R →
      ∃ zn0, N1 z = some zn0 ∧ TReach N1 t r z ∧ zn0.leaf = zn.leaf ∧
        (zn0.liveAt t).length ≤ (zn.liveAt t).length ∧
        ∀ c v, (c, v) ∈ zn.liveAt t → (∃ c', (c', v) ∈ zn0.liveAt t) ∨ v = R := by
    intro z zn hz hzR hzx hzS hzRR
    have hzR0 : TReach N1 t r z := by
      rcases hR' z hzR with h' | h' | h'
      · exact h'
      · exact absurd h' hzS
      · exact absurd h' hzRR
    by_cases hzq : z = q
    · subst hzq
      rw [hN2q] at hz
      cases hz
      refine ⟨qn, hqn, hzR0, hq2l.symm, hq2len, fun c v hc => ?_⟩
      rcases hq2 c v hc with ⟨_, hv⟩ | ⟨_, hc'⟩
      · exact Or.inr hv
      · exact Or.inl ⟨c, hc'⟩
    · rw [hother z hzx hzq hzS hzRR] at hz
      exact ⟨zn, hz, hzR0, rfl, Nat.le_refl _, fun c v hc => Or.inl ⟨c, hc⟩⟩
  refine liveEdges_of_sim p N1 N2 t r r h ?_ ?_
  · intro rn' hrn'
    by_cases hrx : r = x
    · rw [hrx, hN2x] at hrn'; cases hrn'; exact rootOK_half p t f hfH
    obtain ⟨hr2, hr3⟩ := hnew r TReach.root
    obtain ⟨rn0, hr0, _, hl, hlen, _⟩ := hsame r rn' hrn' TReach.root hrx hr2 hr3
    exact rootOK_grow t rn0 rn' (h.1 rn0 hr0) hl.symm hlen
  · intro u un c z zn hu hun hc hzn
    by_cases hzx : z = x
    · subst hzx; rw [hN2x] at hzn; cases hzn; exact Or.inl (childOK_half p t un f hfH)
    by_cases hzS : z = S
    · subst hzS; rw [hN2S] at hzn; cases hzn; exact Or.inl (childOK_half p t un s hsH)
    have hsrc : u ≠ R → ∃ u0 un0, N1 u0 = some un0 ∧ TReach N1 t r u0 ∧ un0.leaf = un.leaf ∧
        ∀ c v, (c, v) ∈ un.liveAt t → (∃ c', (c', v) ∈ un0.liveAt t) ∨ (v = R ∧ u = q) := by
      intro huR
      by_cases hux : u = x
      · subst hux
        rw [hN2x] at hun
        cases hun
        exact ⟨u, vx, hxn, hx, hfl.symm, fun c v hc => Or.inl ⟨c, (hf c v hc).2⟩⟩
      by_cases huS : u = S
      · subst huS
        rw [hN2S] at hun
        cases hun
        refine ⟨x, vx, hxn, hx, hsl.symm, fun c v hc => ?_⟩
        obtain ⟨c0, _, _, hc0⟩ := hs c v hc
        exact Or.inl ⟨c0, hc0⟩
      obtain ⟨un0, hu0, huR0, hl, _, hch⟩ := hsame u un hun hu hux huS huR
      refine ⟨u, un0, hu0, huR0, hl, fun c v hc => ?_⟩
      rcases hch c v hc with h' | hvR
      · exact Or.inl h'
      · by_cases huq : u = q
        · exact Or.inr ⟨hvR, huq⟩
        · exfalso
          subst hvR
          rw [hother u hux huq huS huR] at hun
          exact (hfresh v (Or.inr rfl)).2 u c huR0 ⟨un, hun, hc⟩
    by_cases huR : u = R
    · subst huR
      rw [hN2R] at hun
      cases hun
      rcases hrn c z hc with ⟨_, hz⟩ | ⟨_, hz⟩
      · exact absurd hz hzx
      · exact absurd hz hzS
    obtain ⟨u0, un0, hu0, huR0, hul, hch⟩ := hsrc huR
    by_cases hzR : z = R
    · subst hzR
      rw [hN2R] at hzn
      cases hzn
      rcases hch c z hc with ⟨c', hc'⟩ | ⟨_, huq⟩
      · exact absurd (TReach.link huR0 ⟨un0, hu0, hc'⟩) (fun h' => (hnew _ h').2 rfl)
      · subst huq
        rw [hN2q] at hun
        cases hun
        exact Or.inl (childOK_segRoot p t qn2 rn hql hrn2)
    right
    have hzR2 : TReach N2 t r z := TReach.link hu ⟨un, hun, hc⟩
    obtain ⟨zn0, hz0, _, hzl, hzlen, _⟩ := hsame z zn hzn hzR2 hzx hzS hzR
    rcases hch c z hc with ⟨c', hc'⟩ | ⟨hzy, _⟩
    · exact ⟨u0, un0, c', z, zn0, huR0, hu0, hc', hz0, hul, hzl, hzlen⟩
    · exact absurd hzy hzR

/-! ## The space root's splits -/

/-- `treeOK_rootTimeStep` for `LiveEdges`: the root x's last version y, a new
root of x's kind with x's live pointees and no fewer live klongs. -/
theorem liveEdges_rootTimeStep (p : Params) (N1 N2 : NodeId → Option KNode) (t : Time) (x y : NodeId)
    (vx yn : KNode) (hT : TreeOK N1 t x) (hxn : N1 x = some vx)
    (hN2y : N2 y = some yn) (hyn : ∀ c z, (c, z) ∈ yn.liveAt t → (c, z) ∈ vx.liveAt t)
    (hother : ∀ z, z ≠ x → z ≠ y → N2 z = N1 z)
    (hfy : N1 y = none) (hfresh : ∀ u c', TReach N1 t x u → ¬ TLink N1 t u c' y)
    (hyl : yn.leaf = vx.leaf) (hylen : (vx.liveAt t).length ≤ (yn.liveAt t).length)
    (h : LiveEdges p N1 t x) : LiveEdges p N2 t y := by
  obtain ⟨_, hR'⟩ := treeOK_rootTimeStep N1 N2 t x y vx yn hT hxn hN2y hyn hother hfy hfresh
  have hyR : ∀ v, TReach N1 t x v → v ≠ y := by
    intro v hv hvy; subst hvy
    cases hv with
    | root => rw [hxn] at hfy; cases hfy
    | link hu hl => exact hfresh _ _ hu hl
  have hsame : ∀ z zn, N2 z = some zn → TReach N2 t y z → z ≠ y →
      N1 z = some zn ∧ TReach N1 t x z := by
    intro z zn hz hzR hzy
    obtain ⟨hzR', hzx⟩ := hR' z hzR
    have hzR0 : TReach N1 t x z := by
      rcases hzR' with h' | h'
      · exact h'
      · exact absurd h' hzy
    rw [hother z hzx hzy] at hz
    exact ⟨hz, hzR0⟩
  refine liveEdges_of_sim p N1 N2 t x y h ?_ ?_
  · intro rn hrn
    rw [hN2y] at hrn
    cases hrn
    exact rootOK_grow t vx yn (h.1 vx hxn) hyl hylen
  · intro u un c z zn hu hun hc hzn
    right
    have hsrc : ∃ u0 un0, N1 u0 = some un0 ∧ TReach N1 t x u0 ∧ un0.leaf = un.leaf ∧
        ∀ c v, (c, v) ∈ un.liveAt t → (c, v) ∈ un0.liveAt t := by
      by_cases huy : u = y
      · subst huy
        rw [hN2y] at hun
        cases hun
        exact ⟨x, vx, hxn, TReach.root, hyl.symm, hyn⟩
      · obtain ⟨hu0, huR⟩ := hsame u un hun hu huy
        exact ⟨u, un, hu0, huR, rfl, fun _ _ hc => hc⟩
    obtain ⟨u0, un0, hu0, huR0, hul, hch⟩ := hsrc
    have hc0 := hch c z hc
    have hzy : z ≠ y := fun hzy => hyR z (TReach.link huR0 ⟨un0, hu0, hc0⟩) hzy
    have hzR2 : TReach N2 t y z := TReach.link hu ⟨un, hun, hc⟩
    obtain ⟨hz0, _⟩ := hsame z zn hzn hzR2 hzy
    exact ⟨u0, un0, c, z, zn, huR0, hu0, hc0, hz0, hul, rfl, Nat.le_refl _⟩

/-- `treeOK_rootSpaceStep` for `LiveEdges`: the root x's halves F, S (x's kind,
x's live pointees, `HalfOK`) under a new inner root R with two live klongs or
more. -/
theorem liveEdges_rootSpaceStep (p : Params) (N1 N2 : NodeId → Option KNode) (t : Time) (x F S R : NodeId)
    (vx f s rn : KNode) (sc : Nat) (loc : Nat → Nat) (hsc : 0 < sc)
    (hT : TreeOK N1 t x) (hxn : N1 x = some vx)
    (hN2R : N2 R = some rn) (hrn : ∀ c z, (c, z) ∈ rn.liveAt t → (c = 0 ∧ z = F) ∨ (c = sc ∧ z = S))
    (hN2F : N2 F = some f) (hN2S : N2 S = some s)
    (hf : ∀ c z, (c, z) ∈ f.liveAt t → c < sc ∧ (c, z) ∈ vx.liveAt t)
    (hs : ∀ c z, (c, z) ∈ s.liveAt t → ∃ c0, sc ≤ c0 ∧ c = loc c0 ∧ (c0, z) ∈ vx.liveAt t)
    (hother : ∀ z, z ≠ x → z ≠ F → z ≠ S → z ≠ R → N2 z = N1 z)
    (hfresh : ∀ z, (z = F ∨ z = S ∨ z = R) → N1 z = none ∧ ∀ u c', TReach N1 t x u → ¬ TLink N1 t u c' z)
    (hFS : F ≠ S) (hFR : F ≠ R) (hSR : S ≠ R)
    (hfl : f.leaf = vx.leaf) (hsl : s.leaf = vx.leaf) (hfH : HalfOK p t f) (hsH : HalfOK p t s)
    (hrn2 : 2 ≤ (rn.liveAt t).length)
    (h : LiveEdges p N1 t x) : LiveEdges p N2 t R := by
  obtain ⟨_, hR'⟩ := treeOK_rootSpaceStep N1 N2 t x F S R vx f s rn sc loc hsc hT hxn hN2R hrn hN2F
    hN2S hf hs hother hfresh hFS hFR hSR
  have hnew : ∀ z, (z = F ∨ z = S ∨ z = R) → ∀ v, TReach N1 t x v → v ≠ z := by
    intro z hz v hv hvz; subst hvz
    obtain ⟨hn, hfr⟩ := hfresh v hz
    cases hv with
    | root => rw [hxn] at hn; cases hn
    | link hu hl => exact hfr _ _ hu hl
  have hsame : ∀ z zn, N2 z = some zn → TReach N2 t R z → z ≠ F → z ≠ S → z ≠ R →
      N1 z = some zn ∧ TReach N1 t x z := by
    intro z zn hz hzR hzF hzS hzRR
    obtain ⟨hzR', hzx⟩ := hR' z hzR
    have hzR0 : TReach N1 t x z := by
      rcases hzR' with h' | h' | h' | h'
      · exact h'
      · exact absurd h' hzF
      · exact absurd h' hzS
      · exact absurd h' hzRR
    rw [hother z hzx hzF hzS hzRR] at hz
    exact ⟨hz, hzR0⟩
  refine liveEdges_of_sim p N1 N2 t x R h ?_ ?_
  · intro rn' hrn'
    rw [hN2R] at hrn'
    cases hrn'
    exact rootOK_two t rn hrn2
  · intro u un c z zn hu hun hc hzn
    by_cases hzF : z = F
    · subst hzF; rw [hN2F] at hzn; cases hzn; exact Or.inl (childOK_half p t un f hfH)
    by_cases hzS : z = S
    · subst hzS; rw [hN2S] at hzn; cases hzn; exact Or.inl (childOK_half p t un s hsH)
    by_cases huR : u = R
    · subst huR
      rw [hN2R] at hun
      cases hun
      rcases hrn c z hc with ⟨_, hz⟩ | ⟨_, hz⟩
      · exact absurd hz hzF
      · exact absurd hz hzS
    right
    have hsrc : ∃ u0 un0, N1 u0 = some un0 ∧ TReach N1 t x u0 ∧ un0.leaf = un.leaf ∧
        ∀ c v, (c, v) ∈ un.liveAt t → ∃ c', (c', v) ∈ un0.liveAt t := by
      by_cases huF : u = F
      · subst huF
        rw [hN2F] at hun
        cases hun
        exact ⟨x, vx, hxn, TReach.root, hfl.symm, fun c v hc => ⟨c, (hf c v hc).2⟩⟩
      by_cases huS : u = S
      · subst huS
        rw [hN2S] at hun
        cases hun
        refine ⟨x, vx, hxn, TReach.root, hsl.symm, fun c v hc => ?_⟩
        obtain ⟨c0, _, _, hc0⟩ := hs c v hc
        exact ⟨c0, hc0⟩
      obtain ⟨hu0, huR0⟩ := hsame u un hun hu huF huS huR
      exact ⟨u, un, hu0, huR0, rfl, fun c v hc => ⟨c, hc⟩⟩
    obtain ⟨u0, un0, hu0, huR0, hul, hch⟩ := hsrc
    obtain ⟨c', hc'⟩ := hch c z hc
    have hzRR : z ≠ R := fun h' => hnew R (Or.inr (Or.inr rfl)) z (TReach.link huR0 ⟨un0, hu0, hc'⟩) h'
    have hzR2 : TReach N2 t R z := TReach.link hu ⟨un, hun, hc⟩
    obtain ⟨hz0, _⟩ := hsame z zn hzn hzR2 hzF hzS hzRR
    exact ⟨u0, un0, c', z, zn, huR0, hu0, hc', hz0, hul, rfl, Nat.le_refl _⟩

/-- `treeOK_rootSpaceInPlaceStep` for `LiveEdges`: the root x keeps its first
half f, the new S the second (`HalfOK`, x's kind, x's live pointees), under a
new inner root R with two live klongs or more. -/
theorem liveEdges_rootSpaceInPlaceStep (p : Params) (N1 N2 : NodeId → Option KNode) (t : Time)
    (x S R : NodeId) (vx f s rn : KNode) (sc : Nat) (loc : Nat → Nat) (hsc : 0 < sc)
    (hT : TreeOK N1 t x) (hxn : N1 x = some vx)
    (hN2R : N2 R = some rn) (hrn : ∀ c z, (c, z) ∈ rn.liveAt t → (c = 0 ∧ z = x) ∨ (c = sc ∧ z = S))
    (hN2x : N2 x = some f) (hN2S : N2 S = some s)
    (hf : ∀ c z, (c, z) ∈ f.liveAt t → c < sc ∧ (c, z) ∈ vx.liveAt t)
    (hs : ∀ c z, (c, z) ∈ s.liveAt t → ∃ c0, sc ≤ c0 ∧ c = loc c0 ∧ (c0, z) ∈ vx.liveAt t)
    (hother : ∀ z, z ≠ x → z ≠ S → z ≠ R → N2 z = N1 z)
    (hfresh : ∀ z, (z = S ∨ z = R) → N1 z = none ∧ ∀ u c', TReach N1 t x u → ¬ TLink N1 t u c' z)
    (hSR : S ≠ R)
    (hfl : f.leaf = vx.leaf) (hsl : s.leaf = vx.leaf) (hfH : HalfOK p t f) (hsH : HalfOK p t s)
    (hrn2 : 2 ≤ (rn.liveAt t).length)
    (h : LiveEdges p N1 t x) : LiveEdges p N2 t R := by
  obtain ⟨_, hR'⟩ := treeOK_rootSpaceInPlaceStep N1 N2 t x S R vx f s rn sc loc hsc hT hxn hN2R hrn
    hN2x hN2S hf hs hother hfresh hSR
  have hnew : ∀ z, (z = S ∨ z = R) → ∀ v, TReach N1 t x v → v ≠ z := by
    intro z hz v hv hvz; subst hvz
    obtain ⟨hn, hfr⟩ := hfresh v hz
    cases hv with
    | root => rw [hxn] at hn; cases hn
    | link hu hl => exact hfr _ _ hu hl
  have hsame : ∀ z zn, N2 z = some zn → TReach N2 t R z → z ≠ x → z ≠ S → z ≠ R →
      N1 z = some zn ∧ TReach N1 t x z := by
    intro z zn hz hzR hzx hzS hzRR
    have hzR0 : TReach N1 t x z := by
      rcases hR' z hzR with h' | h' | h'
      · exact h'
      · exact absurd h' hzS
      · exact absurd h' hzRR
    rw [hother z hzx hzS hzRR] at hz
    exact ⟨hz, hzR0⟩
  refine liveEdges_of_sim p N1 N2 t x R h ?_ ?_
  · intro rn' hrn'
    rw [hN2R] at hrn'
    cases hrn'
    exact rootOK_two t rn hrn2
  · intro u un c z zn hu hun hc hzn
    by_cases hzx : z = x
    · subst hzx; rw [hN2x] at hzn; cases hzn; exact Or.inl (childOK_half p t un f hfH)
    by_cases hzS : z = S
    · subst hzS; rw [hN2S] at hzn; cases hzn; exact Or.inl (childOK_half p t un s hsH)
    by_cases huR : u = R
    · subst huR
      rw [hN2R] at hun
      cases hun
      rcases hrn c z hc with ⟨_, hz⟩ | ⟨_, hz⟩
      · exact absurd hz hzx
      · exact absurd hz hzS
    right
    have hsrc : ∃ u0 un0, N1 u0 = some un0 ∧ TReach N1 t x u0 ∧ un0.leaf = un.leaf ∧
        ∀ c v, (c, v) ∈ un.liveAt t → ∃ c', (c', v) ∈ un0.liveAt t := by
      by_cases hux : u = x
      · subst hux
        rw [hN2x] at hun
        cases hun
        exact ⟨u, vx, hxn, TReach.root, hfl.symm, fun c v hc => ⟨c, (hf c v hc).2⟩⟩
      by_cases huS : u = S
      · subst huS
        rw [hN2S] at hun
        cases hun
        refine ⟨x, vx, hxn, TReach.root, hsl.symm, fun c v hc => ?_⟩
        obtain ⟨c0, _, _, hc0⟩ := hs c v hc
        exact ⟨c0, hc0⟩
      obtain ⟨hu0, huR0⟩ := hsame u un hun hu hux huS huR
      exact ⟨u, un, hu0, huR0, rfl, fun c v hc => ⟨c, hc⟩⟩
    obtain ⟨u0, un0, hu0, huR0, hul, hch⟩ := hsrc
    obtain ⟨c', hc'⟩ := hch c z hc
    have hzRR : z ≠ R := fun h' => hnew R (Or.inr rfl) z (TReach.link huR0 ⟨un0, hu0, hc'⟩) h'
    have hzR2 : TReach N2 t R z := TReach.link hu ⟨un, hun, hc⟩
    obtain ⟨hz0, _⟩ := hsame z zn hzn hzR2 hzx hzS hzRR
    exact ⟨u0, un0, c', z, zn, huR0, hu0, hc', hz0, hul, rfl, Nat.le_refl _⟩

end SIS.Tree
