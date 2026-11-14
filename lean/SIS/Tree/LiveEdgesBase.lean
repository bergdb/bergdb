/-
`LiveCounts` edge by edge, its basic part (bergdb 024-12, TP7): `LiveEdges`
states the conditions of `LiveCounts` on the root and on each link of the tree
reached. The space root has a live klong unless it is a segment leaf, and two
if it is inner (`RootOK`). The node a link names has a live klong; two if a
segment leaf names it and it is inner; m if an inner node names it and the
merges are on (`ChildOK`). A step of the writer then checks only the links it
changes: a node that keeps its kind and live pointees and loses no live klong
(`liveEdges_updN_grow`), a fresh copy (`liveEdges_copy`), a change off the tree
(`liveEdges_of_agree`), and the halves of a space split (`HalfOK`). The
equivalence with `LiveCounts` is in `LiveEdges.lean`; this part sits below the
writer's cascade walk (`WriterTreeChainG.lean`).
-/
import SIS.Tree.WriterTreeChainTree

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- The conditions on a node named by a live klong of un. -/
def ChildOK (p : Params) (t : Time) (un yn : KNode) : Prop :=
  yn.liveAt t ≠ [] ∧ (un.leaf = true → yn.leaf = false → 2 ≤ (yn.liveAt t).length) ∧
    (un.leaf = false → p.merges = true → p.mergeBelow ≤ (yn.liveAt t).length)

/-- The conditions on the space root. -/
def RootOK (t : Time) (rn : KNode) : Prop :=
  (rn.liveAt t = [] → rn.leaf = true) ∧ (rn.leaf = false → 2 ≤ (rn.liveAt t).length)

/-- `LiveCounts` link by link. -/
def LiveEdges (p : Params) (N : NodeId → Option KNode) (t : Time) (r : NodeId) : Prop :=
  (∀ rn, N r = some rn → RootOK t rn) ∧
  ∀ u un c y yn, TReach N t r u → N u = some un → (c, y) ∈ un.liveAt t → N y = some yn →
    ChildOK p t un yn

theorem childOK_grow (p : Params) (t : Time) (un un' yn yn' : KNode) (h : ChildOK p t un yn)
    (hu : un'.leaf = un.leaf) (hy : yn'.leaf = yn.leaf)
    (hlen : (yn.liveAt t).length ≤ (yn'.liveAt t).length) : ChildOK p t un' yn' := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun hE => ?_, fun hl hyl => ?_, fun hl hm => ?_⟩
  · have h0 : (yn'.liveAt t).length = 0 := by rw [hE]; rfl
    exact h1 (List.eq_nil_of_length_eq_zero (by omega))
  · rw [hu] at hl; rw [hy] at hyl; have := h2 hl hyl; omega
  · rw [hu] at hl; have := h3 hl hm; omega

/-- A node x whose klongs keep its kind, name live only what it named live or
no node, and lose no live klong keeps `LiveEdges`. -/
theorem liveEdges_updN_grow (p : Params) (N : NodeId → Option KNode) (t : Time) (r x : NodeId)
    (n n' : KNode) (hx : N x = some n) (hl : n'.leaf = n.leaf)
    (hch : ∀ c y, (c, y) ∈ n'.liveAt t → (∃ c', (c', y) ∈ n.liveAt t) ∨ updN N x n' y = none)
    (hlen : (n.liveAt t).length ≤ (n'.liveAt t).length) (h : LiveEdges p N t r) :
    LiveEdges p (updN N x n') t r := by
  have hreach : ∀ u, TReach (updN N x n') t r u → TReach N t r u ∨ updN N x n' u = none := by
    intro u hu
    induction hu with
    | root => exact Or.inl TReach.root
    | @link u c y _ hl' ih =>
      obtain ⟨m, hm, hc⟩ := hl'
      rcases ih with ih | ih
      · by_cases hux : u = x
        · subst hux
          rw [updN_self] at hm
          cases hm
          rcases hch c y hc with ⟨c', hc'⟩ | hy
          · exact Or.inl (TReach.link ih ⟨n, hx, hc'⟩)
          · exact Or.inr hy
        · rw [updN_ne _ _ _ _ hux] at hm
          exact Or.inl (TReach.link ih ⟨m, hm, hc⟩)
      · rw [hm] at ih; cases ih
  refine ⟨fun rn hrn => ?_, fun u un c y yn hu hun hc hyn => ?_⟩
  · by_cases hrx : r = x
    · subst hrx
      rw [updN_self] at hrn
      cases hrn
      obtain ⟨h1, h2⟩ := h.1 n hx
      refine ⟨fun hE => ?_, fun hl' => ?_⟩
      · have h0 : (n'.liveAt t).length = 0 := by rw [hE]; rfl
        rw [hl]; exact h1 (List.eq_nil_of_length_eq_zero (by omega))
      · rw [hl] at hl'; have := h2 hl'; omega
    · rw [updN_ne _ _ _ _ hrx] at hrn
      exact h.1 rn hrn
  · have hu' : TReach N t r u := by
      rcases hreach u hu with h' | h'
      · exact h'
      · rw [hun] at h'; cases h'
    by_cases hux : u = x
    · subst hux
      rw [updN_self] at hun
      cases hun
      rcases hch c y hc with ⟨c', hc'⟩ | hy
      · by_cases hyx : y = u
        · subst hyx
          rw [updN_self] at hyn
          cases hyn
          exact childOK_grow p t n n' n n' (h.2 y n c' y n hu' hx hc' hx) hl hl hlen
        · rw [updN_ne _ _ _ _ hyx] at hyn
          exact childOK_grow p t n n' yn yn (h.2 u n c' y yn hu' hx hc' hyn) hl rfl (Nat.le_refl _)
      · rw [hy] at hyn; cases hyn
    · rw [updN_ne _ _ _ _ hux] at hun
      by_cases hyx : y = x
      · subst hyx
        rw [updN_self] at hyn
        cases hyn
        exact childOK_grow p t un un n n' (h.2 u un c y n hu' hun hc hx) rfl hl hlen
      · rw [updN_ne _ _ _ _ hyx] at hyn
        exact h.2 u un c y yn hu' hun hc hyn

/-! ## A node replaced by a fresh copy -/

/-- The tree after a node x below q is copied to a fresh node y, with x's kind
and live klongs, and q's klong to x points to y (q's kind and number of live
klongs kept): the nodes reached are the ones before but x, and y. -/
theorem tReach_copy (N : NodeId → Option KNode) (t : Time) (r x y q : NodeId) (n n' qn qn' : KNode)
    (k : Nat) (hT : TreeOK N t r) (hx : N x = some n) (hq : N q = some qn) (hqR : TReach N t r q)
    (hk : (k, x) ∈ qn.liveAt t) (hqx : q ≠ x) (hyx : y ≠ x) (hyq : y ≠ q) (hy : N y = none)
    (hyfresh : ∀ u c, TReach N t r u → ¬ TLink N t u c y)
    (hn' : n'.liveAt t = n.liveAt t)
    (hq' : ∀ c z, (c, z) ∈ qn'.liveAt t → ((c, z) ∈ qn.liveAt t ∧ z ≠ x) ∨ (c = k ∧ z = y)) :
    ∀ u, TReach (updN (updN N y n') q qn') t r u → (TReach N t r u ∧ u ≠ x) ∨ u = y := by
  have hxR : TReach N t r x := TReach.link hqR ⟨qn, hq, hk⟩
  have hnotx : ∀ u c, TReach N t r u → TLink N t u c x → u = q := by
    intro u c hu hl
    exact (hT.oneLink u c q k x hu hqR hl ⟨qn, hq, hk⟩).1
  have hrx : r ≠ x := by
    intro h
    exact hT.rootFree q k hqR (h ▸ ⟨qn, hq, hk⟩)
  have hyR : ∀ v, TReach N t r v → v ≠ y := by
    intro v hv hvy
    subst hvy
    cases hv with
    | root => obtain ⟨m, hm⟩ := hT.rootKey; rw [hm] at hy; cases hy
    | link hu hl => exact hyfresh _ _ hu hl
  intro u hu
  induction hu with
  | root => exact Or.inl ⟨TReach.root, hrx⟩
  | @link u c z _ hl ih =>
    obtain ⟨m, hm, hc⟩ := hl
    rcases ih with ⟨ihR, ihx⟩ | ihy
    · by_cases huq : u = q
      · subst huq
        rw [updN_self] at hm
        cases hm
        rcases hq' c z hc with ⟨hc', hzx⟩ | ⟨_, hzy⟩
        · exact Or.inl ⟨TReach.link ihR ⟨qn, hq, hc'⟩, hzx⟩
        · exact Or.inr hzy
      · have huy : u ≠ y := hyR u ihR
        rw [updN_ne _ _ _ _ huq, updN_ne _ _ _ _ huy] at hm
        have hzR : TReach N t r z := TReach.link ihR ⟨m, hm, hc⟩
        refine Or.inl ⟨hzR, fun hzx => ?_⟩
        subst hzx
        exact huq (hnotx u c ihR ⟨m, hm, hc⟩)
    · subst ihy
      rw [updN_ne _ _ _ _ hyq, updN_self] at hm
      cases hm
      rw [hn'] at hc
      have hzR : TReach N t r z := TReach.link hxR ⟨n, hx, hc⟩
      refine Or.inl ⟨hzR, fun hzx => ?_⟩
      subst hzx
      exact hqx (hnotx _ c hxR ⟨n, hx, hc⟩).symm

/-- A time split to a new node keeps `LiveEdges`: x copied to a fresh y with
its kind and live klongs, and x's parent q pointing its klong to y with its
kind and its number of live klongs kept. -/
theorem liveEdges_copy (p : Params) (N : NodeId → Option KNode) (t : Time) (r x y q : NodeId)
    (n n' qn qn' : KNode) (k : Nat) (hT : TreeOK N t r) (hx : N x = some n) (hq : N q = some qn)
    (hqR : TReach N t r q) (hk : (k, x) ∈ qn.liveAt t) (hqx : q ≠ x) (hyx : y ≠ x) (hyq : y ≠ q)
    (hy : N y = none) (hyfresh : ∀ u c, TReach N t r u → ¬ TLink N t u c y)
    (hn'l : n'.leaf = n.leaf) (hn' : n'.liveAt t = n.liveAt t)
    (hq'l : qn'.leaf = qn.leaf) (hq'n : (qn'.liveAt t).length = (qn.liveAt t).length)
    (hq' : ∀ c z, (c, z) ∈ qn'.liveAt t → ((c, z) ∈ qn.liveAt t ∧ z ≠ x) ∨ (c = k ∧ z = y))
    (h : LiveEdges p N t r) : LiveEdges p (updN (updN N y n') q qn') t r := by
  have hreach := tReach_copy N t r x y q n n' qn qn' k hT hx hq hqR hk hqx hyx hyq hy hyfresh hn' hq'
  have hxR : TReach N t r x := TReach.link hqR ⟨qn, hq, hk⟩
  have hyR : ∀ v, TReach N t r v → v ≠ y := by
    intro v hv hvy
    subst hvy
    cases hv with
    | root => obtain ⟨m, hm⟩ := hT.rootKey; rw [hm] at hy; cases hy
    | link hu hl => exact hyfresh _ _ hu hl
  -- every node of the tree after, as a node of the tree before with its kind and count
  have hsim : ∀ v vn, updN (updN N y n') q qn' v = some vn →
      ∃ v0 vn0, N v0 = some vn0 ∧ vn0.leaf = vn.leaf ∧
        (vn0.liveAt t).length = (vn.liveAt t).length ∧ (vn.liveAt t = [] ↔ vn0.liveAt t = []) ∧
        (v = y → v0 = x) ∧ (v ≠ y → v0 = v) := by
    intro v vn hv
    by_cases hvq : v = q
    · subst hvq
      rw [updN_self] at hv
      cases hv
      refine ⟨v, qn, hq, hq'l.symm, hq'n.symm, ?_, fun h => absurd h (Ne.symm hyq), fun _ => rfl⟩
      constructor
      · intro hE; apply List.eq_nil_of_length_eq_zero; rw [← hq'n, hE]; rfl
      · intro hE; apply List.eq_nil_of_length_eq_zero; rw [hq'n, hE]; rfl
    · rw [updN_ne _ _ _ _ hvq] at hv
      by_cases hvy : v = y
      · subst hvy
        rw [updN_self] at hv
        cases hv
        exact ⟨x, n, hx, hn'l.symm, by rw [hn'], by rw [hn'], fun _ => rfl, fun h => absurd rfl h⟩
      · rw [updN_ne _ _ _ _ hvy] at hv
        exact ⟨v, vn, hv, rfl, rfl, Iff.rfl, fun h => absurd h hvy, fun _ => rfl⟩
  have hchild : ∀ (un0 un yn0 yn : KNode), ChildOK p t un0 yn0 → un0.leaf = un.leaf →
      yn0.leaf = yn.leaf → (yn0.liveAt t).length = (yn.liveAt t).length →
      (yn.liveAt t = [] ↔ yn0.liveAt t = []) → ChildOK p t un yn := by
    intro un0 un yn0 yn ⟨h1, h2, h3⟩ hu hy' hl he
    refine ⟨fun hE => h1 (he.mp hE), fun hl1 hl2 => ?_, fun hl1 hm => ?_⟩
    · rw [← hu] at hl1; rw [← hy'] at hl2; have := h2 hl1 hl2; omega
    · rw [← hu] at hl1; have := h3 hl1 hm; omega
  refine ⟨fun rn hrn => ?_, fun u un c z zn hu hun hc hzn => ?_⟩
  · obtain ⟨v0, vn0, hv0, hl, hlen, he, hy0, hny⟩ := hsim r rn hrn
    have hry : r ≠ y := hyR r TReach.root
    have := hny hry; subst this
    obtain ⟨h1, h2⟩ := h.1 vn0 hv0
    refine ⟨fun hE => ?_, fun hl' => ?_⟩
    · rw [← hl]; exact h1 (he.mp hE)
    · rw [← hl] at hl'; have := h2 hl'; omega
  · obtain ⟨u0, un0, hu0, hul, hulen, _, huy, hun'⟩ := hsim u un hun
    obtain ⟨z0, zn0, hz0, hzl, hzlen, hze, hzy, hzn'⟩ := hsim z zn hzn
    -- the link before
    have hlink : TReach N t r u0 ∧ (c, z0) ∈ un0.liveAt t := by
      rcases hreach u hu with ⟨huR, _⟩ | huy'
      · have hu0u : u0 = u := hun' (hyR u huR)
        subst u0
        by_cases huq : u = q
        · subst huq
          rw [updN_self] at hun
          cases hun
          rw [hq] at hu0; cases hu0
          rcases hq' c z hc with ⟨hc', _⟩ | ⟨hck, hzy'⟩
          · have hzy2 : z ≠ y := by
              intro h'; subst h'; exact hyfresh u c huR ⟨qn, hq, hc'⟩
            have hz0z : z0 = z := hzn' hzy2
            subst z0
            exact ⟨huR, hc'⟩
          · have hz0x : z0 = x := hzy hzy'
            subst z0 hck
            exact ⟨huR, hk⟩
        · rw [updN_ne _ _ _ _ huq, updN_ne _ _ _ _ (hyR u huR)] at hun
          rw [hun] at hu0; cases hu0
          have hzy2 : z ≠ y := by
            intro h'; subst h'; exact hyfresh u c huR ⟨un, hun, hc⟩
          have hz0z : z0 = z := hzn' hzy2
          subst z0
          exact ⟨huR, hc⟩
      · have hu0x : u0 = x := huy huy'
        subst u0
        subst huy'
        rw [updN_ne _ _ _ _ hyq, updN_self] at hun
        cases hun
        rw [hx] at hu0; cases hu0
        rw [hn'] at hc
        have hzy2 : z ≠ u := by
          intro h'; subst h'; exact hyfresh x c hxR ⟨n, hx, hc⟩
        have hz0z : z0 = z := hzn' hzy2
        subst z0
        exact ⟨hxR, hc⟩
    exact hchild un0 un zn0 zn (h.2 u0 un0 c z0 zn0 hlink.1 hu0 hlink.2 hz0) hul hzl hzlen hze

/-! ## Agreement, and the space splits -/

/-- A change that leaves the nodes reached as they are keeps `LiveEdges`. -/
theorem liveEdges_of_agree (p : Params) (N N' : NodeId → Option KNode) (t : Time) (r : NodeId)
    (hag : ∀ x, TReach N t r x → N' x = N x) (h : LiveEdges p N t r) : LiveEdges p N' t r := by
  have hR := tReach_of_agree N N' t r hag
  refine ⟨fun rn hrn => ?_, fun u un c z zn hu hun hc hzn => ?_⟩
  · rw [hag r TReach.root] at hrn
    exact h.1 rn hrn
  · have hu' := hR u hu
    rw [hag u hu'] at hun
    have hz' : TReach N t r z := TReach.link hu' ⟨un, hun, hc⟩
    rw [hag z hz'] at hzn
    exact h.2 u un c z zn hu' hun hc hzn

/-- A node any parent may name: a live klong, two at least, and m with the
merges on (a space split's half). -/
def HalfOK (p : Params) (t : Time) (zn : KNode) : Prop :=
  zn.liveAt t ≠ [] ∧ 2 ≤ (zn.liveAt t).length ∧
    (p.merges = true → p.mergeBelow ≤ (zn.liveAt t).length)

theorem childOK_half (p : Params) (t : Time) (un zn : KNode) (h : HalfOK p t zn) :
    ChildOK p t un zn :=
  ⟨h.1, fun _ _ => h.2.1, fun _ hm => h.2.2 hm⟩

theorem rootOK_half (p : Params) (t : Time) (zn : KNode) (h : HalfOK p t zn) : RootOK t zn :=
  ⟨fun hE => absurd hE h.1, fun _ => h.2.1⟩

/-- A space split in place below an inner node: v keeps the first half f, a
fresh S the second half s, both with v's kind, live pointees of v's, and the
counts of `HalfOK`; v's parent q gets S (its kind kept, no live klong lost, its
live pointees q's or S). -/
theorem liveEdges_splitInner (p : Params) (N : NodeId → Option KNode) (t : Time) (r v S q : NodeId)
    (n f s qn q' : KNode) (hv : N v = some n) (hvR : TReach N t r v) (hq : N q = some qn)
    (hT : TreeOK N t r)
    (hSv : S ≠ v) (hSq : S ≠ q) (hvq : v ≠ q) (hS : N S = none)
    (hSfresh : ∀ u c, TReach N t r u → ¬ TLink N t u c S)
    (hfl : f.leaf = n.leaf) (hsl : s.leaf = n.leaf)
    (hfch : ∀ c z, (c, z) ∈ f.liveAt t → ∃ c', (c', z) ∈ n.liveAt t)
    (hsch : ∀ c z, (c, z) ∈ s.liveAt t → ∃ c', (c', z) ∈ n.liveAt t)
    (hfH : HalfOK p t f) (hsH : HalfOK p t s)
    (hq'l : q'.leaf = qn.leaf) (hq'len : (qn.liveAt t).length ≤ (q'.liveAt t).length)
    (hq'ch : ∀ c z, (c, z) ∈ q'.liveAt t → (c, z) ∈ qn.liveAt t ∨ z = S)
    (h : LiveEdges p N t r) :
    LiveEdges p (updN (updN (updN N v f) S s) q q') t r := by
  have hSR : ∀ u, TReach N t r u → u ≠ S := by
    intro u hu huS
    subst huS
    cases hu with
    | root => obtain ⟨m, hm⟩ := hT.rootKey; rw [hm] at hS; cases hS
    | link hu' hl => exact hSfresh _ _ hu' hl
  have hqR : ∀ u, TReach (updN (updN (updN N v f) S s) q q') t r u → TReach N t r u ∨ u = S := by
    intro u hu
    induction hu with
    | root => exact Or.inl TReach.root
    | @link u c z _ hl ih =>
      obtain ⟨m, hm, hc⟩ := hl
      by_cases huq : u = q
      · subst huq
        rw [updN_self] at hm
        cases hm
        rcases hq'ch c z hc with hc' | hz
        · rcases ih with ih | ih
          · exact Or.inl (TReach.link ih ⟨qn, hq, hc'⟩)
          · exact absurd ih (Ne.symm hSq)
        · exact Or.inr hz
      · rw [updN_ne _ _ _ _ huq] at hm
        by_cases huS : u = S
        · subst huS
          rw [updN_self] at hm
          cases hm
          obtain ⟨c', hc'⟩ := hsch c z hc
          exact Or.inl (TReach.link hvR ⟨n, hv, hc'⟩)
        · rw [updN_ne _ _ _ _ huS] at hm
          rcases ih with ih | ih
          · by_cases huv : u = v
            · subst huv
              rw [updN_self] at hm
              cases hm
              obtain ⟨c', hc'⟩ := hfch c z hc
              exact Or.inl (TReach.link ih ⟨n, hv, hc'⟩)
            · rw [updN_ne _ _ _ _ huv] at hm
              exact Or.inl (TReach.link ih ⟨m, hm, hc⟩)
          · exact absurd ih huS
  -- a node after, but the halves, as a node before with its kind and no more live klongs
  have hsim : ∀ z zn, updN (updN (updN N v f) S s) q q' z = some zn → z ≠ v → z ≠ S →
      ∃ zn0, N z = some zn0 ∧ zn0.leaf = zn.leaf ∧ (zn0.liveAt t).length ≤ (zn.liveAt t).length := by
    intro z zn hz hzv hzS
    by_cases hzq : z = q
    · subst hzq
      rw [updN_self] at hz
      cases hz
      exact ⟨qn, hq, hq'l.symm, hq'len⟩
    · rw [updN_ne _ _ _ _ hzq, updN_ne _ _ _ _ hzS, updN_ne _ _ _ _ hzv] at hz
      exact ⟨zn, hz, rfl, Nat.le_refl _⟩
  refine ⟨fun rn hrn => ?_, fun u un c z zn hu hun hc hzn => ?_⟩
  · have hrS : r ≠ S := hSR r TReach.root
    by_cases hrv : r = v
    · rw [hrv, updN_ne _ _ _ _ hvq, updN_ne _ _ _ _ (Ne.symm hSv), updN_self] at hrn
      cases hrn
      exact rootOK_half p t f hfH
    · obtain ⟨rn0, hr0, hl, hlen⟩ := hsim r rn hrn hrv hrS
      obtain ⟨h1, h2⟩ := h.1 rn0 hr0
      refine ⟨fun hE => ?_, fun hl' => ?_⟩
      · have h0 : (rn.liveAt t).length = 0 := by rw [hE]; rfl
        rw [← hl]; exact h1 (List.eq_nil_of_length_eq_zero (by omega))
      · rw [← hl] at hl'; have := h2 hl'; omega
  · -- the halves: any parent may name them
    by_cases hzv : z = v
    · rw [hzv, updN_ne _ _ _ _ hvq, updN_ne _ _ _ _ (Ne.symm hSv), updN_self] at hzn
      cases hzn
      exact childOK_half p t un f hfH
    by_cases hzS : z = S
    · rw [hzS, updN_ne _ _ _ _ hSq, updN_self] at hzn
      cases hzn
      exact childOK_half p t un s hsH
    obtain ⟨zn0, hz0, hzl, hzlen⟩ := hsim z zn hzn hzv hzS
    -- the link before
    have hlink : ∃ u0 un0 c0, TReach N t r u0 ∧ N u0 = some un0 ∧ un0.leaf = un.leaf ∧
        (c0, z) ∈ un0.liveAt t := by
      by_cases huq : u = q
      · subst huq
        rw [updN_self] at hun
        cases hun
        rcases hq'ch c z hc with hc' | hz
        · rcases hqR u hu with hu' | hu'
          · exact ⟨u, qn, c, hu', hq, hq'l.symm, hc'⟩
          · exact absurd hu' (Ne.symm hSq)
        · exact absurd hz hzS
      · rw [updN_ne _ _ _ _ huq] at hun
        by_cases huS : u = S
        · subst huS
          rw [updN_self] at hun
          cases hun
          obtain ⟨c', hc'⟩ := hsch c z hc
          exact ⟨v, n, c', hvR, hv, hsl.symm, hc'⟩
        · rw [updN_ne _ _ _ _ huS] at hun
          have hu' : TReach N t r u := by
            rcases hqR u hu with h' | h'
            · exact h'
            · exact absurd h' huS
          by_cases huv : u = v
          · subst huv
            rw [updN_self] at hun
            cases hun
            obtain ⟨c', hc'⟩ := hfch c z hc
            exact ⟨u, n, c', hu', hv, hfl.symm, hc'⟩
          · rw [updN_ne _ _ _ _ huv] at hun
            exact ⟨u, un, c, hu', hun, rfl, hc⟩
    obtain ⟨u0, un0, c0, hu0, hun0, hul, hc0⟩ := hlink
    exact childOK_grow p t un0 un zn0 zn (h.2 u0 un0 c0 z zn0 hu0 hun0 hc0 hz0) hul.symm hzl.symm hzlen

end SIS.Tree
