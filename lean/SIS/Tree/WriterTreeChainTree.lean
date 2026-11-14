/-
The tree steps of the splits inside a cascade (bergdb 024-22, `OpTreeOK`), on
the virtual trees of `writerWP_appendKlongs_chainG`: N1 the tree with the
klongs put into x (a tree that is not the writer's), N2 the tree after the
split, with the klongs to the new nodes put into the parent (or the tree at
the end). Each step keeps a tree and says what N2 reaches.
-/
import SIS.Tree.WriterTreeChainSteps
import SIS.Tree.WriterGetMerge

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- A space split in place of x below q: x keeps its klongs below sc, the new
node S those at or above it under local names, and q's new node has the klong
(sc, S) and else q's live klongs. -/
theorem treeOK_spaceInPlaceStep (N1 N2 : NodeId → Option KNode) (t : Time) (r q x S : NodeId)
    (qn vx f s qn' : KNode) (k1 sc : Nat) (loc : Nat → Nat)
    (hT : TreeOK N1 t r) (hq : TReach N1 t r q) (hqn : N1 q = some qn) (hqk : (k1, x) ∈ qn.liveAt t)
    (hxn : N1 x = some vx)
    (hN2q : N2 q = some qn')
    (hq' : ∀ c z, (c, z) ∈ qn'.liveAt t → (c = sc ∧ z = S) ∨ (c ≠ sc ∧ (c, z) ∈ qn.liveAt t))
    (hN2x : N2 x = some f) (hN2S : N2 S = some s)
    (hf : ∀ c z, (c, z) ∈ f.liveAt t → c < sc ∧ (c, z) ∈ vx.liveAt t)
    (hs : ∀ c z, (c, z) ∈ s.liveAt t → ∃ c0, sc ≤ c0 ∧ c = loc c0 ∧ (c0, z) ∈ vx.liveAt t)
    (hother : ∀ z, z ≠ x → z ≠ q → z ≠ S → N2 z = N1 z)
    (hfS : N1 S = none) (hfresh : ∀ u c', TReach N1 t r u → ¬ TLink N1 t u c' S) :
    TreeOK N2 t r ∧ ∀ z, TReach N2 t r z → TReach N1 t r z ∨ z = S := by
  have hqx_link : TLink N1 t q k1 x := ⟨qn, hqn, hqk⟩
  have hx : TReach N1 t r x := TReach.link hq hqx_link
  have hqx : q ≠ x := fun h => hT.no_self_link q k1 hq (by rw [← h] at hqx_link; exact hqx_link)
  have hxS : x ≠ S := fun h => by rw [h, hfS] at hxn; cases hxn
  have hqS : q ≠ S := fun h => by rw [h, hfS] at hqn; cases hqn
  have hql : ∀ c' z, TLink N2 t q c' z → (c' = sc ∧ z = S) ∨ (c' ≠ sc ∧ (c', z) ∈ qn.liveAt t) := by
    intro c' z hl
    obtain ⟨mm, hm, hc⟩ := hl
    rw [hN2q] at hm; simp only [Option.some.injEq] at hm; subst hm
    exact hq' c' z hc
  have hxl : ∀ c' z, TLink N2 t x c' z → TLink N1 t x c' z ∧ c' < sc := by
    intro c' z hl
    obtain ⟨mm, hm, hc⟩ := hl
    rw [hN2x] at hm; simp only [Option.some.injEq] at hm; subst hm
    exact ⟨⟨vx, hxn, (hf c' z hc).2⟩, (hf c' z hc).1⟩
  have hSl : ∀ c' z, TLink N2 t S c' z → ∃ c0, sc ≤ c0 ∧ c' = loc c0 ∧ TLink N1 t x c0 z := by
    intro c' z hl
    obtain ⟨mm, hm, hc⟩ := hl
    rw [hN2S] at hm; simp only [Option.some.injEq] at hm; subst hm
    obtain ⟨c0, h1, h2, h3⟩ := hs c' z hc
    exact ⟨c0, h1, h2, ⟨vx, hxn, h3⟩⟩
  have hOld : ∀ u, u ≠ x → u ≠ q → u ≠ S → ∀ c' z, TLink N2 t u c' z → TLink N1 t u c' z := by
    intro u h1 h2 h3 c' z hl
    obtain ⟨mm, hm, hc⟩ := hl
    rw [hother u h1 h2 h3] at hm
    exact ⟨mm, hm, hc⟩
  have hnotR : ∀ z, z = S → ¬ TReach N1 t r z := by
    intro z hz; rw [hz]; exact not_reach_fresh N1 t r S hT hfS hfresh
  have hr' : (r = r ∧ ¬ (fun _ : NodeId => False) r) ∨ ((fun z => z = S) r ∧ ∀ y' c,
      (TReach N1 t r y' ∨ (fun z => z = S) y') → ¬ (fun _ : NodeId => False) y' →
      ¬ TLink N2 t y' c r) := Or.inl ⟨rfl, fun h => h⟩
  have hlinks : ∀ u c' z, (TReach N1 t r u ∨ (fun z => z = S) u) → ¬ (fun _ : NodeId => False) u →
      TLink N2 t u c' z → (fun z => z = S) z ∨ (¬ (fun _ : NodeId => False) z ∧ ∃ y0 c0,
        TReach N1 t r y0 ∧ TLink N1 t y0 c0 z ∧ (fun u c' => if u = x then
          (if c' < sc then (x, c') else (S, loc c')) else (u, c')) y0 c0 = (u, c')) := by
    intro u c' z hu _ hl
    by_cases huS : u = S
    · rw [huS] at hl
      obtain ⟨c0, hge, hcc, hl0⟩ := hSl c' z hl
      have hnlt : ¬ c0 < sc := by omega
      exact Or.inr ⟨fun h => h, x, c0, hx, hl0, by simp [huS, hnlt, hcc]⟩
    · have huR : TReach N1 t r u := hu.elim id (fun h => absurd h huS)
      by_cases hux : u = x
      · rw [hux] at hl
        obtain ⟨hl0, hlt⟩ := hxl c' z hl
        exact Or.inr ⟨fun h => h, x, c', hx, hl0, by simp [hux, hlt]⟩
      · by_cases huq : u = q
        · rw [huq] at hl
          rcases hql c' z hl with ⟨_, h⟩ | ⟨_, hm⟩
          · exact Or.inl h
          · exact Or.inr ⟨fun h => h, q, c', hq, ⟨qn, hqn, hm⟩, by simp [hqx, huq]⟩
        · exact Or.inr ⟨fun h => h, u, c', huR, hOld u hux huq huS c' z hl, by simp [hux]⟩
  refine ⟨?_, fun z hz => (tReach_transfer_gone N1 N2 t r r (fun z => z = S) (fun _ => False) _ hr'
    hlinks (fun _ _ h => h) z hz).1⟩
  apply treeOK_transfer_gone N1 N2 t r r (fun z => z = S) (fun _ => False) _ hT hnotR hr' hlinks
  · intro u c' u' c'' z hu _ hu' _ hz hl1 hl2
    have hz' : z = S := hz
    have hone : ∀ v d, (TReach N1 t r v ∨ v = S) → TLink N2 t v d z → v = q ∧ d = sc := by
      intro v d hv hl
      rw [hz'] at hl
      by_cases hvS : v = S
      · rw [hvS] at hl
        obtain ⟨c0, _, _, hl0⟩ := hSl d S hl
        exact absurd hl0 (hfresh x c0 hx)
      · have hvR : TReach N1 t r v := hv.elim id (fun h => absurd h hvS)
        by_cases hvx : v = x
        · rw [hvx] at hl; exact absurd (hxl d S hl).1 (hfresh x d hx)
        · by_cases hvq : v = q
          · rw [hvq] at hl
            rcases hql d S hl with ⟨hd, _⟩ | ⟨_, hm⟩
            · exact ⟨hvq, hd⟩
            · exact absurd ⟨qn, hqn, hm⟩ (hfresh q d hq)
          · exact absurd (hOld v hvx hvq hvS d S hl) (hfresh v d hvR)
    obtain ⟨a1, b1⟩ := hone u c' hu hl1
    obtain ⟨a2, b2⟩ := hone u' c'' hu' hl2
    exact ⟨a1.trans a2.symm, b1.trans b2.symm⟩
  · intro z _ h; exact h
  · by_cases hrq : r = q
    · rw [hrq, hN2q]; exact ⟨_, rfl⟩
    · by_cases hrx : r = x
      · rw [hrx, hN2x]; exact ⟨_, rfl⟩
      · obtain ⟨rm, hrm⟩ := hT.rootKey
        have hrS : r ≠ S := fun h => by rw [h, hfS] at hrm; cases hrm
        rw [hother r hrx hrq hrS]; exact ⟨rm, hrm⟩

/-- A new node R between q and its child x: q's klong k1 names R, and R's one
live klong, the empty key, names x. -/
theorem treeOK_insertAbove (N1 N2 : NodeId → Option KNode) (t : Time) (r q x R : NodeId)
    (qn qn2 rn : KNode) (k1 : Nat)
    (hT : TreeOK N1 t r) (hq : TReach N1 t r q) (hqn : N1 q = some qn) (hqk : (k1, x) ∈ qn.liveAt t)
    (hN2q : N2 q = some qn2)
    (hq2 : ∀ c z, (c, z) ∈ qn2.liveAt t → (c = k1 ∧ z = R) ∨ (c ≠ k1 ∧ (c, z) ∈ qn.liveAt t))
    (hN2R : N2 R = some rn) (hrn : ∀ c z, (c, z) ∈ rn.liveAt t → c = 0 ∧ z = x)
    (hother : ∀ z, z ≠ q → z ≠ R → N2 z = N1 z)
    (hfR : N1 R = none) (hfresh : ∀ u c', TReach N1 t r u → ¬ TLink N1 t u c' R) :
    TreeOK N2 t r ∧ ∀ z, TReach N2 t r z → TReach N1 t r z ∨ z = R := by
  have hqx_link : TLink N1 t q k1 x := ⟨qn, hqn, hqk⟩
  have hx : TReach N1 t r x := TReach.link hq hqx_link
  have hqR : q ≠ R := fun h => by rw [h, hfR] at hqn; cases hqn
  have hql : ∀ c' z, TLink N2 t q c' z → (c' = k1 ∧ z = R) ∨ (c' ≠ k1 ∧ (c', z) ∈ qn.liveAt t) := by
    intro c' z hl
    obtain ⟨mm, hm, hc⟩ := hl
    rw [hN2q] at hm; simp only [Option.some.injEq] at hm; subst hm
    exact hq2 c' z hc
  have hRl : ∀ c' z, TLink N2 t R c' z → c' = 0 ∧ z = x := by
    intro c' z hl
    obtain ⟨mm, hm, hc⟩ := hl
    rw [hN2R] at hm; simp only [Option.some.injEq] at hm; subst hm
    exact hrn c' z hc
  have hOld : ∀ u, u ≠ q → u ≠ R → ∀ c' z, TLink N2 t u c' z → TLink N1 t u c' z := by
    intro u h1 h2 c' z hl
    obtain ⟨mm, hm, hc⟩ := hl
    rw [hother u h1 h2] at hm
    exact ⟨mm, hm, hc⟩
  have hnotR : ∀ z, z = R → ¬ TReach N1 t r z := by
    intro z hz; rw [hz]; exact not_reach_fresh N1 t r R hT hfR hfresh
  have hr' : (r = r ∧ ¬ (fun _ : NodeId => False) r) ∨ ((fun z => z = R) r ∧ ∀ y' c,
      (TReach N1 t r y' ∨ (fun z => z = R) y') → ¬ (fun _ : NodeId => False) y' →
      ¬ TLink N2 t y' c r) := Or.inl ⟨rfl, fun h => h⟩
  have hlinks : ∀ u c' z, (TReach N1 t r u ∨ (fun z => z = R) u) → ¬ (fun _ : NodeId => False) u →
      TLink N2 t u c' z → (fun z => z = R) z ∨ (¬ (fun _ : NodeId => False) z ∧ ∃ y0 c0,
        TReach N1 t r y0 ∧ TLink N1 t y0 c0 z ∧ (fun u c' => if u = q ∧ c' = k1 then (R, 0)
          else (u, c')) y0 c0 = (u, c')) := by
    intro u c' z hu _ hl
    by_cases huR : u = R
    · rw [huR] at hl
      obtain ⟨hc, hz⟩ := hRl c' z hl
      exact Or.inr ⟨fun h => h, q, k1, hq, by rw [hz]; exact hqx_link, by simp [huR, hc]⟩
    · have huR' : TReach N1 t r u := hu.elim id (fun h => absurd h huR)
      by_cases huq : u = q
      · rw [huq] at hl
        rcases hql c' z hl with ⟨_, h⟩ | ⟨hc, hm⟩
        · exact Or.inl h
        · exact Or.inr ⟨fun h => h, q, c', hq, ⟨qn, hqn, hm⟩, by simp [huq, hc]⟩
      · exact Or.inr ⟨fun h => h, u, c', huR', hOld u huq huR c' z hl, by simp [huq]⟩
  refine ⟨?_, fun z hz => (tReach_transfer_gone N1 N2 t r r (fun z => z = R) (fun _ => False) _ hr'
    hlinks (fun _ _ h => h) z hz).1⟩
  apply treeOK_transfer_gone N1 N2 t r r (fun z => z = R) (fun _ => False) _ hT hnotR hr' hlinks
  · intro u c' u' c'' z hu _ hu' _ hz hl1 hl2
    have hz' : z = R := hz
    have hone : ∀ v d, (TReach N1 t r v ∨ v = R) → TLink N2 t v d z → v = q ∧ d = k1 := by
      intro v d hv hl
      rw [hz'] at hl
      by_cases hvR : v = R
      · rw [hvR] at hl
        have := (hRl d R hl).2
        rw [← this] at hx
        exact absurd hx (hnotR R rfl)
      · have hvR' : TReach N1 t r v := hv.elim id (fun h => absurd h hvR)
        by_cases hvq : v = q
        · rw [hvq] at hl
          rcases hql d R hl with ⟨hd, _⟩ | ⟨_, hm⟩
          · exact ⟨hvq, hd⟩
          · exact absurd ⟨qn, hqn, hm⟩ (hfresh q d hq)
        · exact absurd (hOld v hvq hvR d R hl) (hfresh v d hvR')
    obtain ⟨a1, b1⟩ := hone u c' hu hl1
    obtain ⟨a2, b2⟩ := hone u' c'' hu' hl2
    exact ⟨a1.trans a2.symm, b1.trans b2.symm⟩
  · intro z _ h; exact h
  · by_cases hrq : r = q
    · rw [hrq, hN2q]; exact ⟨_, rfl⟩
    · obtain ⟨rm, hrm⟩ := hT.rootKey
      have hrR : r ≠ R := fun h => by rw [h, hfR] at hrm; cases hrm
      rw [hother r hrq hrR]; exact ⟨rm, hrm⟩

/-- The space root x replaced by a new node y: y's live klongs are x's. -/
theorem treeOK_rootTimeStep (N1 N2 : NodeId → Option KNode) (t : Time) (x y : NodeId)
    (vx yn : KNode) (hT : TreeOK N1 t x) (hxn : N1 x = some vx)
    (hN2y : N2 y = some yn) (hyn : ∀ c z, (c, z) ∈ yn.liveAt t → (c, z) ∈ vx.liveAt t)
    (hother : ∀ z, z ≠ x → z ≠ y → N2 z = N1 z)
    (hfy : N1 y = none) (hfresh : ∀ u c', TReach N1 t x u → ¬ TLink N1 t u c' y) :
    TreeOK N2 t y ∧ ∀ z, TReach N2 t y z → (TReach N1 t x z ∨ z = y) ∧ z ≠ x := by
  have hxy : x ≠ y := fun h => by rw [h, hfy] at hxn; cases hxn
  have hyl : ∀ c' z, TLink N2 t y c' z → TLink N1 t x c' z := by
    intro c' z hl
    obtain ⟨mm, hm, hc⟩ := hl
    rw [hN2y] at hm; simp only [Option.some.injEq] at hm; subst hm
    exact ⟨vx, hxn, hyn c' z hc⟩
  have hOld : ∀ u, u ≠ x → u ≠ y → ∀ c' z, TLink N2 t u c' z → TLink N1 t u c' z := by
    intro u h1 h2 c' z hl
    obtain ⟨mm, hm, hc⟩ := hl
    rw [hother u h1 h2] at hm
    exact ⟨mm, hm, hc⟩
  have hnotR : ∀ z, z = y → ¬ TReach N1 t x z := by
    intro z hz; rw [hz]; exact not_reach_fresh N1 t x y hT hfy hfresh
  have hr' : (y = x ∧ ¬ (fun z => z = x) x) ∨ ((fun z => z = y) y ∧ ∀ y' c,
      (TReach N1 t x y' ∨ (fun z => z = y) y') → ¬ (fun z => z = x) y' →
      ¬ TLink N2 t y' c y) := by
    refine Or.inr ⟨rfl, fun u c hu hug hl => ?_⟩
    have hux : u ≠ x := hug
    by_cases huy : u = y
    · rw [huy] at hl
      exact hfresh x c TReach.root (hyl c y hl)
    · have huR : TReach N1 t x u := hu.elim id (fun h => absurd h huy)
      exact hfresh u c huR (hOld u hux huy c y hl)
  have hlinks : ∀ u c' z, (TReach N1 t x u ∨ (fun z => z = y) u) → ¬ (fun z => z = x) u →
      TLink N2 t u c' z → (fun z => z = y) z ∨ (¬ (fun z => z = x) z ∧ ∃ y0 c0,
        TReach N1 t x y0 ∧ TLink N1 t y0 c0 z ∧ (fun u c' => if u = x then (y, c') else (u, c'))
          y0 c0 = (u, c')) := by
    intro u c' z hu hug hl
    have hux : u ≠ x := hug
    by_cases huy : u = y
    · rw [huy] at hl
      have hl0 := hyl c' z hl
      refine Or.inr ⟨fun hz => ?_, x, c', TReach.root, hl0, by simp [huy]⟩
      have hz' : z = x := hz
      rw [hz'] at hl0
      exact hT.rootFree x c' TReach.root hl0
    · have huR : TReach N1 t x u := hu.elim id (fun h => absurd h huy)
      have hl0 := hOld u hux huy c' z hl
      refine Or.inr ⟨fun hz => ?_, u, c', huR, hl0, by simp [hux]⟩
      have hz' : z = x := hz
      rw [hz'] at hl0
      exact hT.rootFree u c' huR hl0
  have hNewGone : ∀ z, (fun z => z = y) z → ¬ (fun z => z = x) z := by
    intro z h1 h2
    have h1' : z = y := h1
    have h2' : z = x := h2
    exact hxy (h2'.symm.trans h1')
  refine ⟨?_, fun z hz => tReach_transfer_gone N1 N2 t x y (fun z => z = y) (fun z => z = x) _ hr'
    hlinks hNewGone z hz⟩
  apply treeOK_transfer_gone N1 N2 t x y (fun z => z = y) (fun z => z = x) _ hT hnotR hr' hlinks
  · intro u c' u' c'' z hu hug hu' hug' hz hl1 hl2
    have hz' : z = y := hz
    have hno : ∀ v d, (TReach N1 t x v ∨ v = y) → v ≠ x → ¬ TLink N2 t v d z := by
      intro v d hv hvx hl
      rw [hz'] at hl
      by_cases hvy : v = y
      · rw [hvy] at hl; exact hfresh x d TReach.root (hyl d y hl)
      · have hvR : TReach N1 t x v := hv.elim id (fun h => absurd h hvy)
        exact hfresh v d hvR (hOld v hvx hvy d y hl)
    exact absurd hl1 (hno u c' hu hug)
  · exact hNewGone
  · exact ⟨yn, hN2y⟩


theorem mrg_R0_liveAt (t : Time) (x : NodeId) :
    ∀ c z, (c, z) ∈ (⟨false, newKlongs t [(0, x)]⟩ : KNode).liveAt t ↔ c = 0 ∧ z = x := by
  intro c z
  rw [mrg_newKlongs_liveAt_iff false t [(0, x)] (by simp) c z]
  simp

/-- A space split of x below a segment leaf q: halves F and S under a new
segment root R, whose live klongs are (0, F) and (sc, S); q's klong k1 names
R; x is left behind. -/
theorem treeOK_segSpaceStep (N1 N2 : NodeId → Option KNode) (t : Time) (r q x F S R : NodeId)
    (qn vx f s rn qn2 : KNode) (k1 sc : Nat) (loc : Nat → Nat) (hsc : 0 < sc)
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
    (hFS : F ≠ S) (hFR : F ≠ R) (hSR : S ≠ R) :
    TreeOK N2 t r ∧ ∀ z, TReach N2 t r z → (TReach N1 t r z ∨ z = F ∨ z = S ∨ z = R) ∧ z ≠ x := by
  obtain ⟨hFN, hFF⟩ := hfresh F (Or.inl rfl)
  obtain ⟨hSN, hSF⟩ := hfresh S (Or.inr (Or.inl rfl))
  obtain ⟨hRN, hRF⟩ := hfresh R (Or.inr (Or.inr rfl))
  have hqx_link : TLink N1 t q k1 x := ⟨qn, hqn, hqk⟩
  have hx : TReach N1 t r x := TReach.link hq hqx_link
  have hqR : q ≠ R := fun h => by rw [h, hRN] at hqn; cases hqn
  have hxR : x ≠ R := fun h => by rw [h, hRN] at hxn; cases hxn
  have hqx : q ≠ x := fun h => hT.no_self_link q k1 hq (by rw [← h] at hqx_link; exact hqx_link)
  have hRm := mrg_R0_liveAt t x
  let Nm : NodeId → Option KNode := fun z =>
    if z = R then some ⟨false, newKlongs t [(0, x)]⟩ else if z = q then some qn2 else N1 z
  have hNmR : Nm R = some ⟨false, newKlongs t [(0, x)]⟩ := by simp [Nm]
  have hNmq : Nm q = some qn2 := by simp [Nm, hqR]
  have hNmo : ∀ z, z ≠ q → z ≠ R → Nm z = N1 z := by intro z h1 h2; simp [Nm, h1, h2]
  obtain ⟨hTm, hRm'⟩ := treeOK_insertAbove N1 Nm t r q x R qn qn2 _ k1 hT hq hqn hqk hNmq hq2 hNmR
    (fun c z h => (hRm c z).mp h) hNmo hRN hRF
  -- q and R are reached in the tree with R
  have hqm : TReach Nm t r q := by
    obtain ⟨a, ha⟩ := hq.pathLen
    apply tReach_of_agree_short N1 Nm t r a q ha
    intro y k hk hka
    have hyq : y ≠ q := fun he => by
      rw [he] at hk; have := PathLen.depth_unique hT a q k ha hk; omega
    have hyR : y ≠ R := fun he => not_reach_fresh N1 t r R hT hRN hRF (he ▸ hk.reach)
    exact hNmo y hyq hyR
  have hRreach : TReach Nm t r R := TReach.link hqm ⟨qn2, hNmq, hq2k⟩
  have hNmx : Nm x = some vx := by rw [hNmo x (Ne.symm hqx) hxR]; exact hxn
  -- what the tree with R links: no link to F or S
  have hNmF : ∀ z, (z = F ∨ z = S) → Nm z = none ∧ ∀ u c', TReach Nm t r u → ¬ TLink Nm t u c' z := by
    intro z hz
    have hzq : z ≠ q := fun h => by
      rcases hz with h' | h' <;> rw [← h, h'] at hqn
      · rw [hFN] at hqn; cases hqn
      · rw [hSN] at hqn; cases hqn
    have hzR : z ≠ R := by rcases hz with h' | h' <;> rw [h'] <;> assumption
    have hzN : N1 z = none := by rcases hz with h' | h' <;> rw [h'] <;> assumption
    have hzF : ∀ u c', TReach N1 t r u → ¬ TLink N1 t u c' z := by
      rcases hz with h' | h' <;> rw [h'] <;> assumption
    refine ⟨by rw [hNmo z hzq hzR]; exact hzN, fun u c' hu hl => ?_⟩
    obtain ⟨mm, hm, hc⟩ := hl
    by_cases huR : u = R
    · rw [huR, hNmR] at hm; simp only [Option.some.injEq] at hm; subst hm
      have := ((hRm c' z).mp hc).2
      rw [this] at hzN; rw [hzN] at hxn; cases hxn
    · by_cases huq : u = q
      · rw [huq, hNmq] at hm; simp only [Option.some.injEq] at hm; subst hm
        rcases hq2 c' z hc with ⟨_, h⟩ | ⟨_, h⟩
        · exact hzR h
        · exact hzF q c' hq ⟨qn, hqn, h⟩
      · rw [hNmo u huq huR] at hm
        have huN : TReach N1 t r u := by
          rcases hRm' u hu with h | h
          · exact h
          · exact absurd h huR
        exact hzF u c' huN ⟨mm, hm, hc⟩
  obtain ⟨hTF, hFm⟩ := hNmF F (Or.inl rfl)
  obtain ⟨hTS, hSm⟩ := hNmF S (Or.inr rfl)
  obtain ⟨hT2, hR2⟩ := treeOK_spaceSplit_gen Nm N2 t r R x F S ⟨false, newKlongs t [(0, x)]⟩ vx f s rn
    0 sc loc hTm hRreach hNmR ((hRm 0 x).mpr ⟨rfl, rfl⟩) hNmx hN2R
    (by
      intro c z hc
      rcases hrn c z hc with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inr (Or.inl ⟨by omega, h1, h2⟩)
      · exact Or.inl ⟨h1, h2⟩)
    hN2F hN2S hf hs
    (by
      intro z h1 h2 h3 h4
      by_cases hzq : z = q
      · rw [hzq, hN2q, hNmq]
      · rw [hother z h1 hzq h3 h4 h2, hNmo z hzq h2])
    hTF hTS hFS
    (by
      intro z hz
      rcases hz with h | h
      · rw [h]; exact hFm
      · rw [h]; exact hSm)
  refine ⟨hT2, fun z hz => ?_⟩
  obtain ⟨h1, h2⟩ := hR2 z hz
  refine ⟨?_, h2⟩
  rcases h1 with h | h | h
  · rcases hRm' z h with h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inr (Or.inr h'))
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))


/-- A space split in place of x below a segment leaf q: x keeps its klongs
below sc, the new node S those at or above it, a new segment root R has (0, x)
and (sc, S), and q's klong k1 names R. -/
theorem treeOK_segSpaceInPlaceStep (N1 N2 : NodeId → Option KNode) (t : Time) (r q x S R : NodeId)
    (qn vx f s rn qn2 : KNode) (k1 sc : Nat) (loc : Nat → Nat) (hsc : 0 < sc)
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
    (hSR : S ≠ R) :
    TreeOK N2 t r ∧ ∀ z, TReach N2 t r z → TReach N1 t r z ∨ z = S ∨ z = R := by
  obtain ⟨hSN, hSF⟩ := hfresh S (Or.inl rfl)
  obtain ⟨hRN, hRF⟩ := hfresh R (Or.inr rfl)
  have hqx_link : TLink N1 t q k1 x := ⟨qn, hqn, hqk⟩
  have hqR : q ≠ R := fun h => by rw [h, hRN] at hqn; cases hqn
  have hxR : x ≠ R := fun h => by rw [h, hRN] at hxn; cases hxn
  have hqx : q ≠ x := fun h => hT.no_self_link q k1 hq (by rw [← h] at hqx_link; exact hqx_link)
  have hRm := mrg_R0_liveAt t x
  let Nm : NodeId → Option KNode := fun z =>
    if z = R then some ⟨false, newKlongs t [(0, x)]⟩ else if z = q then some qn2 else N1 z
  have hNmR : Nm R = some ⟨false, newKlongs t [(0, x)]⟩ := by simp [Nm]
  have hNmq : Nm q = some qn2 := by simp [Nm, hqR]
  have hNmo : ∀ z, z ≠ q → z ≠ R → Nm z = N1 z := by intro z h1 h2; simp [Nm, h1, h2]
  obtain ⟨hTm, hRm'⟩ := treeOK_insertAbove N1 Nm t r q x R qn qn2 _ k1 hT hq hqn hqk hNmq hq2 hNmR
    (fun c z h => (hRm c z).mp h) hNmo hRN hRF
  have hqm : TReach Nm t r q := by
    obtain ⟨a, ha⟩ := hq.pathLen
    apply tReach_of_agree_short N1 Nm t r a q ha
    intro y k hk hka
    have hyq : y ≠ q := fun he => by
      rw [he] at hk; have := PathLen.depth_unique hT a q k ha hk; omega
    have hyR : y ≠ R := fun he => not_reach_fresh N1 t r R hT hRN hRF (he ▸ hk.reach)
    exact hNmo y hyq hyR
  have hRreach : TReach Nm t r R := TReach.link hqm ⟨qn2, hNmq, hq2k⟩
  have hNmx : Nm x = some vx := by rw [hNmo x (Ne.symm hqx) hxR]; exact hxn
  have hSq : S ≠ q := fun h => by rw [← h, hSN] at hqn; cases hqn
  have hNmS : Nm S = none := by rw [hNmo S hSq hSR]; exact hSN
  have hSm : ∀ u c', TReach Nm t r u → ¬ TLink Nm t u c' S := by
    intro u c' hu hl
    obtain ⟨mm, hm, hc⟩ := hl
    by_cases huR : u = R
    · rw [huR, hNmR] at hm; simp only [Option.some.injEq] at hm; subst hm
      have := ((hRm c' S).mp hc).2
      rw [this] at hSN; rw [hSN] at hxn; cases hxn
    · by_cases huq : u = q
      · rw [huq, hNmq] at hm; simp only [Option.some.injEq] at hm; subst hm
        rcases hq2 c' S hc with ⟨_, h⟩ | ⟨_, h⟩
        · exact hSR h
        · exact hSF q c' hq ⟨qn, hqn, h⟩
      · rw [hNmo u huq huR] at hm
        have huN : TReach N1 t r u := by
          rcases hRm' u hu with h | h
          · exact h
          · exact absurd h huR
        exact hSF u c' huN ⟨mm, hm, hc⟩
  obtain ⟨hT2, hR2⟩ := treeOK_spaceInPlaceStep Nm N2 t r R x S ⟨false, newKlongs t [(0, x)]⟩ vx f s rn
    0 sc loc hTm hRreach hNmR ((hRm 0 x).mpr ⟨rfl, rfl⟩) hNmx hN2R
    (by
      intro c z hc
      rcases hrn c z hc with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inr ⟨by omega, (hRm c z).mpr ⟨h1, h2⟩⟩
      · exact Or.inl ⟨h1, h2⟩)
    hN2x hN2S hf hs
    (by
      intro z h1 h2 h3
      by_cases hzq : z = q
      · rw [hzq, hN2q, hNmq]
      · rw [hother z h1 hzq h3 h2, hNmo z hzq h2])
    hNmS hSm
  refine ⟨hT2, fun z hz => ?_⟩
  rcases hR2 z hz with h | h
  · rcases hRm' z h with h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inr h')
  · exact Or.inr (Or.inl h)

/-- A space split of the space root x: halves F and S under a new space root R
with (0, F) and (sc, S); x is left behind. -/
theorem treeOK_rootSpaceStep (N1 N2 : NodeId → Option KNode) (t : Time) (x F S R : NodeId)
    (vx f s rn : KNode) (sc : Nat) (loc : Nat → Nat) (hsc : 0 < sc)
    (hT : TreeOK N1 t x) (hxn : N1 x = some vx)
    (hN2R : N2 R = some rn) (hrn : ∀ c z, (c, z) ∈ rn.liveAt t → (c = 0 ∧ z = F) ∨ (c = sc ∧ z = S))
    (hN2F : N2 F = some f) (hN2S : N2 S = some s)
    (hf : ∀ c z, (c, z) ∈ f.liveAt t → c < sc ∧ (c, z) ∈ vx.liveAt t)
    (hs : ∀ c z, (c, z) ∈ s.liveAt t → ∃ c0, sc ≤ c0 ∧ c = loc c0 ∧ (c0, z) ∈ vx.liveAt t)
    (hother : ∀ z, z ≠ x → z ≠ F → z ≠ S → z ≠ R → N2 z = N1 z)
    (hfresh : ∀ z, (z = F ∨ z = S ∨ z = R) → N1 z = none ∧ ∀ u c', TReach N1 t x u → ¬ TLink N1 t u c' z)
    (hFS : F ≠ S) (hFR : F ≠ R) (hSR : S ≠ R) :
    TreeOK N2 t R ∧ ∀ z, TReach N2 t R z → (TReach N1 t x z ∨ z = F ∨ z = S ∨ z = R) ∧ z ≠ x := by
  obtain ⟨hFN, hFF⟩ := hfresh F (Or.inl rfl)
  obtain ⟨hSN, hSF⟩ := hfresh S (Or.inr (Or.inl rfl))
  obtain ⟨hRN, hRF⟩ := hfresh R (Or.inr (Or.inr rfl))
  have hxR : x ≠ R := fun h => by rw [h, hRN] at hxn; cases hxn
  have hRm := mrg_R0_liveAt t x
  let Nm : NodeId → Option KNode := fun z => if z = R then some ⟨false, newKlongs t [(0, x)]⟩ else N1 z
  have hNmR : Nm R = some ⟨false, newKlongs t [(0, x)]⟩ := by simp [Nm]
  have hNmo : ∀ z, z ≠ R → Nm z = N1 z := by intro z h; simp [Nm, h]
  have hTm := treeOK_newRootAbove N1 Nm t x R _ hT hRN hRF hNmR (fun c z h => (hRm c z).mp h) hNmo
  have hRm' := tReach_newRootAbove N1 Nm t x R _ hT hRN hRF hNmR (fun c z h => (hRm c z).mp h) hNmo
  have hNmx : Nm x = some vx := by rw [hNmo x hxR]; exact hxn
  have hNmF : ∀ z, (z = F ∨ z = S) → Nm z = none ∧ ∀ u c', TReach Nm t R u → ¬ TLink Nm t u c' z := by
    intro z hz
    have hzR : z ≠ R := by rcases hz with h' | h' <;> rw [h'] <;> assumption
    have hzN : N1 z = none := by rcases hz with h' | h' <;> rw [h'] <;> assumption
    have hzF : ∀ u c', TReach N1 t x u → ¬ TLink N1 t u c' z := by
      rcases hz with h' | h' <;> rw [h'] <;> assumption
    refine ⟨by rw [hNmo z hzR]; exact hzN, fun u c' hu hl => ?_⟩
    obtain ⟨mm, hm, hc⟩ := hl
    by_cases huR : u = R
    · rw [huR, hNmR] at hm; simp only [Option.some.injEq] at hm; subst hm
      have := ((hRm c' z).mp hc).2
      rw [this] at hzN; rw [hzN] at hxn; cases hxn
    · rw [hNmo u huR] at hm
      have huN : TReach N1 t x u := by
        rcases hRm' u hu with h | h
        · exact absurd h huR
        · exact h
      exact hzF u c' huN ⟨mm, hm, hc⟩
  obtain ⟨hTF, hFm⟩ := hNmF F (Or.inl rfl)
  obtain ⟨hTS, hSm⟩ := hNmF S (Or.inr rfl)
  obtain ⟨hT2, hR2⟩ := treeOK_spaceSplit_gen Nm N2 t R R x F S ⟨false, newKlongs t [(0, x)]⟩ vx f s rn
    0 sc loc hTm TReach.root hNmR ((hRm 0 x).mpr ⟨rfl, rfl⟩) hNmx hN2R
    (by
      intro c z hc
      rcases hrn c z hc with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inr (Or.inl ⟨by omega, h1, h2⟩)
      · exact Or.inl ⟨h1, h2⟩)
    hN2F hN2S hf hs
    (by intro z h1 h2 h3 h4; rw [hother z h1 h3 h4 h2, hNmo z h2])
    hTF hTS hFS
    (by
      intro z hz
      rcases hz with h | h
      · rw [h]; exact hFm
      · rw [h]; exact hSm)
  refine ⟨hT2, fun z hz => ?_⟩
  obtain ⟨h1, h2⟩ := hR2 z hz
  refine ⟨?_, h2⟩
  rcases h1 with h | h | h
  · rcases hRm' z h with h' | h'
    · exact Or.inr (Or.inr (Or.inr h'))
    · exact Or.inl h'
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))

/-- A space split in place of the space root x: x keeps its klongs below sc,
the new node S those at or above it, and a new space root R has (0, x) and
(sc, S). -/
theorem treeOK_rootSpaceInPlaceStep (N1 N2 : NodeId → Option KNode) (t : Time) (x S R : NodeId)
    (vx f s rn : KNode) (sc : Nat) (loc : Nat → Nat) (hsc : 0 < sc)
    (hT : TreeOK N1 t x) (hxn : N1 x = some vx)
    (hN2R : N2 R = some rn) (hrn : ∀ c z, (c, z) ∈ rn.liveAt t → (c = 0 ∧ z = x) ∨ (c = sc ∧ z = S))
    (hN2x : N2 x = some f) (hN2S : N2 S = some s)
    (hf : ∀ c z, (c, z) ∈ f.liveAt t → c < sc ∧ (c, z) ∈ vx.liveAt t)
    (hs : ∀ c z, (c, z) ∈ s.liveAt t → ∃ c0, sc ≤ c0 ∧ c = loc c0 ∧ (c0, z) ∈ vx.liveAt t)
    (hother : ∀ z, z ≠ x → z ≠ S → z ≠ R → N2 z = N1 z)
    (hfresh : ∀ z, (z = S ∨ z = R) → N1 z = none ∧ ∀ u c', TReach N1 t x u → ¬ TLink N1 t u c' z)
    (hSR : S ≠ R) :
    TreeOK N2 t R ∧ ∀ z, TReach N2 t R z → TReach N1 t x z ∨ z = S ∨ z = R := by
  obtain ⟨hSN, hSF⟩ := hfresh S (Or.inl rfl)
  obtain ⟨hRN, hRF⟩ := hfresh R (Or.inr rfl)
  have hxR : x ≠ R := fun h => by rw [h, hRN] at hxn; cases hxn
  have hRm := mrg_R0_liveAt t x
  let Nm : NodeId → Option KNode := fun z => if z = R then some ⟨false, newKlongs t [(0, x)]⟩ else N1 z
  have hNmR : Nm R = some ⟨false, newKlongs t [(0, x)]⟩ := by simp [Nm]
  have hNmo : ∀ z, z ≠ R → Nm z = N1 z := by intro z h; simp [Nm, h]
  have hTm := treeOK_newRootAbove N1 Nm t x R _ hT hRN hRF hNmR (fun c z h => (hRm c z).mp h) hNmo
  have hRm' := tReach_newRootAbove N1 Nm t x R _ hT hRN hRF hNmR (fun c z h => (hRm c z).mp h) hNmo
  have hNmx : Nm x = some vx := by rw [hNmo x hxR]; exact hxn
  have hNmS : Nm S = none := by rw [hNmo S hSR]; exact hSN
  have hSm : ∀ u c', TReach Nm t R u → ¬ TLink Nm t u c' S := by
    intro u c' hu hl
    obtain ⟨mm, hm, hc⟩ := hl
    by_cases huR : u = R
    · rw [huR, hNmR] at hm; simp only [Option.some.injEq] at hm; subst hm
      have := ((hRm c' S).mp hc).2
      rw [this] at hSN; rw [hSN] at hxn; cases hxn
    · rw [hNmo u huR] at hm
      have huN : TReach N1 t x u := by
        rcases hRm' u hu with h | h
        · exact absurd h huR
        · exact h
      exact hSF u c' huN ⟨mm, hm, hc⟩
  obtain ⟨hT2, hR2⟩ := treeOK_spaceInPlaceStep Nm N2 t R R x S ⟨false, newKlongs t [(0, x)]⟩ vx f s rn
    0 sc loc hTm TReach.root hNmR ((hRm 0 x).mpr ⟨rfl, rfl⟩) hNmx hN2R
    (by
      intro c z hc
      rcases hrn c z hc with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inr ⟨by omega, (hRm c z).mpr ⟨h1, h2⟩⟩
      · exact Or.inl ⟨h1, h2⟩)
    hN2x hN2S hf hs
    (by intro z h1 h2 h3; rw [hother z h1 h3 h2, hNmo z h2])
    hNmS hSm
  refine ⟨hT2, fun z hz => ?_⟩
  rcases hR2 z hz with h | h
  · rcases hRm' z h with h' | h'
    · exact Or.inr (Or.inr h')
    · exact Or.inl h'
  · exact Or.inr (Or.inl h)


/-- The halves of a node's last version with klongs put (InsOK), as links of
the node with the klongs put, cut at the divider, a live compare value of the
node above 0. -/
theorem chain_halves_facts (t : Time) (n : KNode) (ins : List (Nat × NodeId)) (hins : InsOK n ins)
    (h2 : 2 ≤ n.live.length) (hnt : ∀ s, Klong.time s ∈ n.ks → s ≤ t) (hnwf : klongsWf n.ks = true) :
    ∃ r : Nat × NodeId, (halves n.leaf t (n.lastVersion t) ins).2.2 = r.1 ∧ 0 < r.1 ∧ r ∈ n.live ∧
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
  refine ⟨r, hdiv, hsc, hrm, ?_, ?_⟩
  · intro c z h
    obtain ⟨h1, h2'⟩ := hfh c z h
    exact ⟨h1, KNode.addKeys_liveAt_of_fold t ins _ hnwf hnt c z h2'⟩
  · intro c z h
    obtain ⟨c0, h1, h2', h3⟩ := hsh c z h
    exact ⟨c0, h1, h2', KNode.addKeys_liveAt_of_fold t ins _ hnwf hnt c0 z h3⟩

/-- A node with links among another's, in place of a node of a tree, keeps a
tree and reaches less. -/
theorem treeOK_updN_sub (N : NodeId → Option KNode) (t : Time) (r x : NodeId) (m m' : KNode)
    (hT : TreeOK (updN N x m) t r) (hsub : ∀ c z, (c, z) ∈ m'.liveAt t → (c, z) ∈ m.liveAt t) :
    TreeOK (updN N x m') t r ∧ ∀ z, TReach (updN N x m') t r z → TReach (updN N x m) t r z := by
  have hl : ∀ y c z, TLink (updN N x m') t y c z → TLink (updN N x m) t y c z := by
    intro y c z hl
    obtain ⟨mm, hm, hc⟩ := hl
    by_cases hy : y = x
    · rw [hy, updN_self] at hm; simp only [Option.some.injEq] at hm; subst hm
      exact ⟨m, by rw [hy, updN_self], hsub c z hc⟩
    · rw [updN_ne _ _ _ _ hy] at hm
      exact ⟨mm, by rw [updN_ne _ _ _ _ hy]; exact hm, hc⟩
  refine ⟨treeOK_of_sublinks _ _ t r hT ?_ hl, ?_⟩
  · by_cases hr : r = x
    · rw [hr, updN_self]; exact ⟨_, rfl⟩
    · obtain ⟨rm, hrm⟩ := hT.rootKey
      rw [updN_ne _ _ _ _ hr] at hrm ⊢; exact ⟨rm, hrm⟩
  · intro z hz
    induction hz with
    | root => exact TReach.root
    | link _ hlk ih => exact TReach.link ih (hl _ _ _ hlk)

end SIS.Tree
