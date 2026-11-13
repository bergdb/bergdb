import SIS.Tree.RangeLeb
import SIS.Tree.WriterTreeMerge

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! A merge keeps the walk's ranges (bergdb 024-12, TP10; `RangeOrder`): two
adjacent siblings l (at cL) and rr (at cR, the next live compare value of their
parent p) are replaced by one new node m1 with their merged live klongs
(`mergeList`: in an inner node rr's empty key gets cR); p names m1 by cL and
loses cR. m1's range after, from l's low bound to rr's high bound, holds both
old ranges, each old child keeps its range (`rangeOrder_mergeOne`). This is
what `PutInv`'s leaf order alone cannot carry (`PutInvRange.lean`). -/

/-- The bound of an old child in the merged node: at most its bound after,
when the old node's compare values lie below B, every later compare value
after is an old one or at least B, and the high bound after is at least B. -/
theorem isNext_hiLE_bound (l0 l : List (Nat × NodeId)) (B : Nat) (hi : Option Nat) (c : Nat)
    (b0 b : Option Nat) (h0 : IsNext l0 (some B) c b0) (h : IsNext l hi c b)
    (hl0B : ∀ r ∈ l0, r.1 < B) (hB : HiLE (some B) hi)
    (hlater : ∀ r ∈ l, c < r.1 → r ∈ l0 ∨ B ≤ r.1) : HiLE b0 b := by
  -- b0 is at most B
  have hb0 : ∃ x, b0 = some x ∧ x ≤ B := by
    rcases h0 with ⟨hb, _⟩ | ⟨r0, hr0, hb, _, _⟩
    · exact ⟨B, hb, Nat.le_refl _⟩
    · exact ⟨r0.1, hb, Nat.le_of_lt (hl0B r0 hr0)⟩
  obtain ⟨x, hx, hxB⟩ := hb0
  rw [hx]
  rcases h with ⟨hb, _⟩ | ⟨r, hr, hb, hlt, _⟩
  · rw [hb]
    have h1 : HiLE (some x) (some B) := ⟨x, rfl, hxB⟩
    exact HiLE.trans _ _ _ h1 hB
  · rw [hb]
    rcases hlater r hr hlt with hr0 | hBr
    · rcases h0 with ⟨_, hall⟩ | ⟨r0, _, hb0', _, hmin⟩
      · have := hall r hr0; omega
      · rw [hx] at hb0'; cases hb0'
        exact ⟨r0.1, rfl, hmin r hr0 hlt⟩
    · exact ⟨x, rfl, Nat.le_trans hxB hBr⟩

/-- A live klong of the tail of a node's live klongs has a compare value above
the head's. -/
theorem live_tail_gt (n : KNode) (a q : Nat × NodeId) (hh : n.live.head? = some a)
    (hq : q ∈ n.live.tail) : a.1 < q.1 := by
  have hs := KNode.live_order n
  cases hl : n.live with
  | nil => rw [hl] at hh; cases hh
  | cons a' rest =>
    rw [hl] at hh hq hs
    simp only [List.head?_cons, Option.some.injEq] at hh
    subst hh
    simp only [List.tail_cons] at hq
    exact (List.pairwise_cons.mp hs).1 q hq

/-- The walk's ranges after a merge into one node: the adjacent siblings l (cL)
and rr (cR, the next live compare value of p after cL) under the inner node p
are replaced by the new node m1, whose live klongs are among their merged ones;
p names m1 by cL and loses cR; l and rr are reached no more. -/
theorem rangeOrder_mergeOne (N N' : NodeId → Option KNode) (t : Time) (r p l rr m1 : NodeId)
    (pn ln rn pn' mn : KNode) (inner : Bool) (cL cR : Nat)
    (hR : RangeOrder N t r) (hT : TreeOK N t r) (hp : TReach N t r p) (hpn : N p = some pn)
    (hpl : pn.leaf = false)
    (hl : (cL, l) ∈ pn.liveAt t) (hrr : (cR, rr) ∈ pn.liveAt t) (hcLR : cL < cR)
    (hadj : ∀ q ∈ pn.liveAt t, cL < q.1 → cR ≤ q.1)
    (hln : N l = some ln) (hrn : N rr = some rn)
    (hlt : ∀ s, Klong.time s ∈ ln.ks → s ≤ t) (hrt : ∀ s, Klong.time s ∈ rn.ks → s ≤ t)
    (hinner : inner = !ln.leaf) (hrl : rn.leaf = ln.leaf)
    (hhead : inner = true → ∃ y, rn.live.head? = some (0, y))
    (hm1 : N m1 = none) (hm1f : ∀ u c, TReach N t r u → ¬ TLink N t u c m1)
    (hN'm1 : N' m1 = some mn) (hml : mn.leaf = ln.leaf)
    (hmn : ∀ c z, (c, z) ∈ mn.liveAt t → (c, z) ∈ mergeList inner cR ln.live rn.live)
    (hN'p : N' p = some pn') (hpl' : pn'.leaf = false)
    (hpn' : ∀ c z, (c, z) ∈ pn'.liveAt t →
      (c = cL ∧ z = m1) ∨ ((c, z) ∈ pn.liveAt t ∧ c ≠ cL ∧ c ≠ cR))
    (hother : ∀ y, y ≠ p → y ≠ l → y ≠ rr → y ≠ m1 → N' y = N y) :
    RangeOrder N' t r := by
  have hlL : ln.liveAt t = ln.live := KNode.liveAt_of_times ln t hlt
  have hrL : rn.liveAt t = rn.live := KNode.liveAt_of_times rn t hrt
  have hlink_l : TLink N t p cL l := ⟨pn, hpn, hl⟩
  have hlink_r : TLink N t p cR rr := ⟨pn, hpn, hrr⟩
  have hlR : TReach N t r l := TReach.link hp hlink_l
  have hrR : TReach N t r rr := TReach.link hp hlink_r
  have hpl0 : p ≠ l := fun h => hT.no_self_link p cL hp (by rw [← h] at hlink_l; exact hlink_l)
  have hpr0 : p ≠ rr := fun h => hT.no_self_link p cR hp (by rw [← h] at hlink_r; exact hlink_r)
  have hm1p : p ≠ m1 := fun h => by rw [h, hm1] at hpn; cases hpn
  have hm1l : l ≠ m1 := fun h => by rw [h, hm1] at hln; cases hln
  have hm1r : rr ≠ m1 := fun h => by rw [h, hm1] at hrn; cases hrn
  have hrootm : r ≠ m1 := by
    intro h; obtain ⟨m, hm⟩ := hT.rootKey; rw [h, hm1] at hm; cases hm
  have hrootl : r ≠ l := fun h => hT.rootFree p cL hp (h ▸ hlink_l)
  have hrootr : r ≠ rr := fun h => hT.rootFree p cR hp (h ▸ hlink_r)
  have hcR0 : cR ≠ 0 := by omega
  -- the only links to l and rr are p's
  have hchild : ∀ u c z, TReach N t r u → TLink N t u c z → u ≠ p → z ≠ l ∧ z ≠ rr ∧ z ≠ m1 := by
    intro u c z hu hlk hup
    refine ⟨fun h => hup (hT.oneLink u c p cL l hu hp (h ▸ hlk) hlink_l).1,
      fun h => hup (hT.oneLink u c p cR rr hu hp (h ▸ hlk) hlink_r).1,
      fun h => hm1f u c hu (h ▸ hlk)⟩
  have hlchild : ∀ c z, (c, z) ∈ ln.live → z ≠ l ∧ z ≠ rr ∧ z ≠ m1 := fun c z h =>
    hchild l c z hlR ⟨ln, hln, by rw [hlL]; exact h⟩ hpl0.symm
  have hrchild : ∀ c z, (c, z) ∈ rn.live → z ≠ l ∧ z ≠ rr ∧ z ≠ m1 := fun c z h =>
    hchild rr c z hrR ⟨rn, hrn, by rw [hrL]; exact h⟩ hpr0.symm
  -- l's bound in p is cR
  have hbl : ∀ hi0, ((cL, l), some cR) ∈ childBounds (pn.liveAt t) hi0 := by
    intro hi0
    apply childBounds_of_isNext _ hi0 (KNode.liveAt_order pn t) _ _ hl
    right
    exact ⟨(cR, rr), hrr, rfl, hcLR, fun r' hr' hlt => hadj r' hr' hlt⟩
  let G : NodeId → Nat → Option Nat → Prop := fun z lo hi =>
    (z ≠ m1 ∧ z ≠ l ∧ z ≠ rr ∧ ∃ lo0 hi0, ReachR N t r z lo0 hi0 ∧ lo ≤ lo0 ∧ HiLE hi0 hi) ∨
    (z = m1 ∧ ∃ lol hir, ReachR N t r l lol (some cR) ∧ ReachR N t r rr cR hir ∧ lo ≤ lol ∧
      lol < cR ∧ UpperBound hir cR ∧ HiLE hir hi)
  -- the merged node's high bound holds cR
  have hBhi : ∀ hir hi, UpperBound hir cR → HiLE hir hi → HiLE (some cR) hi := by
    intro hir hi hu hh
    cases hi with
    | none => trivial
    | some h =>
      obtain ⟨b0, hb0, hle⟩ := hh
      subst hb0
      simp only [UpperBound] at hu
      exact ⟨cR, rfl, by omega⟩
  apply rangeOrder_of_good N' t r G
  · exact Or.inl ⟨hrootm, hrootl, hrootr, 0, none, ReachR.root, Nat.le_refl _, HiLE.refl _⟩
  · intro z lo hi m c z' b _ hG hm hml' hb
    have hcz := childBounds_fst _ _ _ _ hb
    have hms := KNode.liveAt_order m t
    rcases hG with ⟨hzm, hzl, hzr, lo0, hi0, hz0, hlo, hhi⟩ |
      ⟨hzm, lol, hir, hl0, hr0, hlo, hlolt, hiru, hhi⟩
    · by_cases hzp : z = p
      · rw [hzp, hN'p] at hm; cases hm
        rw [hzp] at hz0
        have hpr := hR p lo0 hi0 pn hz0 hpn
        rcases hpn' c z' hcz with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
        · rw [h1, h2] at hb ⊢
          obtain ⟨b0, hb0⟩ := childBounds_exists (pn.liveAt t) hi0 (cR, rr) hrr
          have hrr0 := ReachR.inner p pn lo0 hi0 cR rr b0 hz0 hpn hpl hb0
          rw [ite_zero_eq cR lo0 hcR0] at hrr0
          have hlr0 := ReachR.inner p pn lo0 hi0 cL l (some cR) hz0 hpn hpl (hbl hi0)
          refine Or.inr ⟨rfl, _, b0, hlr0, hrr0, ?_, ?_, ?_, ?_⟩
          · by_cases hk : cL = 0
            · rw [hk]; simp only [beq_self_eq_true, ↓reduceIte]; exact hlo
            · have e1 := ite_zero_eq cL lo hk; have e2 := ite_zero_eq cL lo0 hk; omega
          · by_cases hk : cL = 0
            · rw [hk]; simp only [beq_self_eq_true, ↓reduceIte]
              have := (hpr (cR, rr) hrr).1
              simp only [hpl, Bool.false_eq_true, ↓reduceIte] at this
              omega
            · rw [ite_zero_eq cL lo0 hk]; exact hcLR
          · rcases (childBounds_isNext _ hi0 (KNode.liveAt_order pn t) _ _ hb0).2 with
              ⟨hb', _⟩ | ⟨r', hr', hb', hlt', _⟩
            · rw [hb']; exact (hpr (cR, rr) hrr).2
            · rw [hb']; simp only [UpperBound]; exact hlt'
          · refine isNext_hiLE2 _ _ hi0 hi cR cL b0 b
              (childBounds_isNext _ hi0 (KNode.liveAt_order pn t) _ _ hb0).2
              (childBounds_isNext _ hi hms _ _ hb).2 (Or.inl hhi) (fun r' hr' => (hpr r' hr').2) ?_
            intro r' hr' hlt
            rcases hpn' r'.1 r'.2 hr' with ⟨h3, _⟩ | ⟨h3, h4, h5⟩
            · omega
            · have := hadj r' h3 hlt
              exact ⟨r', h3, by omega, Nat.le_refl _⟩
        · have hz'l : z' ≠ l := fun h => h2 (hT.oneLink p c p cL l hp hp ⟨pn, hpn, h ▸ h1⟩ hlink_l).2
          have hz'r : z' ≠ rr := fun h => h3 (hT.oneLink p c p cR rr hp hp ⟨pn, hpn, h ▸ h1⟩ hlink_r).2
          have hz'm : z' ≠ m1 := fun h => hm1f p c hp ⟨pn, hpn, h ▸ h1⟩
          have hlat : ∀ r' ∈ pn'.liveAt t, c < r'.1 →
              ∃ r0 ∈ pn.liveAt t, c < r0.1 ∧ r0.1 ≤ r'.1 := by
            intro r' hr' hlt
            rcases hpn' r'.1 r'.2 hr' with ⟨h7, _⟩ | ⟨h7, _, _⟩
            · exact ⟨(cL, l), hl, by simp only; omega, by simp only; omega⟩
            · exact ⟨r', h7, hlt, Nat.le_refl _⟩
          obtain ⟨lo1, hi1, h4, h5, h6⟩ := old_child_step N t r hR p pn lo0 lo hi0 hi hz0 hpn hpl hlo
            hhi _ hms c z' z' b h1 hb hlat
          exact Or.inl ⟨hz'm, hz'l, hz'r, lo1, hi1, h4, h5, h6⟩
      · have hm0 : N z = some m := by rw [← hother z hzp hzl hzr hzm]; exact hm
        obtain ⟨hz'l, hz'r, hz'm⟩ := hchild z c z' (reachR_tReach N t r z lo0 hi0 hz0) ⟨m, hm0, hcz⟩
          hzp
        obtain ⟨lo1, hi1, h4, h5, h6⟩ := old_child_step N t r hR z m lo0 lo hi0 hi hz0 hm0 hml' hlo
          hhi _ hms c z' z' b hcz hb (fun r' hr' hlt => ⟨r', hr', hlt, Nat.le_refl _⟩)
        exact Or.inl ⟨hz'm, hz'l, hz'r, lo1, hi1, h4, h5, h6⟩
    · rw [hzm, hN'm1] at hm; cases hm
      have hlnl : ln.leaf = false := by rw [← hml]; exact hml'
      have hrnl : rn.leaf = false := by rw [hrl]; exact hlnl
      have hin : inner = true := by rw [hinner, hlnl]; rfl
      obtain ⟨y0, hy0⟩ := hhead hin
      have hlr := hR l lol (some cR) ln hl0 hln
      have hrr' := hR rr cR hir rn hr0 hrn
      have hB := hBhi hir hi hiru hhi
      -- the later klongs of the merged node
      have hmlater : ∀ q ∈ mn.liveAt t, (q ∈ ln.live) ∨ (cR ≤ q.1 ∧ (q ∈ rn.live.tail ∨ q.1 = cR)) := by
        intro q hq
        rcases mem_mergeList inner cR ln.live rn.live q.1 q.2 (hmn q.1 q.2 hq) with h1 | h1 | ⟨c0, h1, h2⟩
        · exact Or.inl h1
        · have hgt := live_tail_gt rn (0, y0) q hy0 h1
          have hq' : q ∈ rn.liveAt t := by rw [hrL]; exact List.mem_of_mem_tail h1
          have := (hrr' q hq').1
          simp only [hrnl, Bool.false_eq_true, ↓reduceIte] at this
          exact Or.inr ⟨by simp only at hgt; omega, Or.inl h1⟩
        · rw [hin] at h2; simp only [↓reduceIte] at h2
          exact Or.inr ⟨by omega, Or.inr h2⟩
      rcases mem_mergeList inner cR ln.live rn.live c z' (hmn c z' hcz) with h1 | h1 | ⟨c0, h1, h2⟩
      · -- a child of l
        have h1' : (c, z') ∈ ln.liveAt t := by rw [hlL]; exact h1
        obtain ⟨bl, hbl0⟩ := childBounds_exists (ln.liveAt t) (some cR) (c, z') h1'
        obtain ⟨hz'l, hz'r, hz'm⟩ := hlchild c z' h1
        refine Or.inl ⟨hz'm, hz'l, hz'r, _, bl, ReachR.inner l ln lol (some cR) c z' bl hl0 hln hlnl hbl0,
          ?_, ?_⟩
        · by_cases hk : c = 0
          · rw [hk]; simp only [beq_self_eq_true, ↓reduceIte]; exact hlo
          · have e1 := ite_zero_eq c lo hk; have e2 := ite_zero_eq c lol hk; omega
        · refine isNext_hiLE_bound _ _ cR hi c bl b
            (childBounds_isNext _ _ (KNode.liveAt_order ln t) _ _ hbl0).2
            (childBounds_isNext _ hi hms _ _ hb).2 (fun r' hr' => by
              have := (hlr r' hr').2; simp only [UpperBound] at this; exact this) hB ?_
          intro r' hr' _
          rcases hmlater r' hr' with h3 | ⟨h3, _⟩
          · left; rw [hlL]; exact h3
          · right; exact h3
      · -- a child of rr, not its first
        have hgt := live_tail_gt rn (0, y0) (c, z') hy0 h1
        have h1' : (c, z') ∈ rn.liveAt t := by rw [hrL]; exact List.mem_of_mem_tail h1
        have hc0 : c ≠ 0 := by simp only at hgt; omega
        have hcR : cR < c := by
          have := (hrr' (c, z') h1').1
          simp only [hrnl, Bool.false_eq_true, ↓reduceIte] at this
          omega
        obtain ⟨br, hbr⟩ := childBounds_exists (rn.liveAt t) hir (c, z') h1'
        obtain ⟨hz'l, hz'r, hz'm⟩ := hrchild c z' (List.mem_of_mem_tail h1)
        have hz'0 := ReachR.inner rr rn cR hir c z' br hr0 hrn hrnl hbr
        rw [ite_zero_eq c cR hc0] at hz'0
        refine Or.inl ⟨hz'm, hz'l, hz'r, _, br, hz'0,
          by rw [ite_zero_eq c lo hc0]; exact Nat.le_refl _, ?_⟩
        refine isNext_hiLE2 _ _ hir hi c c br b
          (childBounds_isNext _ _ (KNode.liveAt_order rn t) _ _ hbr).2
          (childBounds_isNext _ hi hms _ _ hb).2 (Or.inl hhi) (fun r' hr' => (hrr' r' hr').2) ?_
        intro r' hr' hlt
        rcases hmlater r' hr' with h3 | ⟨_, h3 | h3⟩
        · have := (hlr r' (by rw [hlL]; exact h3)).2
          simp only [UpperBound] at this; omega
        · exact ⟨r', by rw [hrL]; exact List.mem_of_mem_tail h3, hlt, Nat.le_refl _⟩
        · omega
      · -- rr's first child, at cR
        rw [hin] at h2; simp only [↓reduceIte] at h2
        rw [hy0] at h1
        simp only [Option.some.injEq, Prod.mk.injEq] at h1
        obtain ⟨_, hz⟩ := h1
        rw [h2, ← hz] at hb ⊢
        have hy0' : (0, y0) ∈ rn.liveAt t := by rw [hrL]; exact List.mem_of_mem_head? hy0
        obtain ⟨br, hbr⟩ := childBounds_exists (rn.liveAt t) hir (0, y0) hy0'
        obtain ⟨hz'l, hz'r, hz'm⟩ := hrchild 0 y0 (List.mem_of_mem_head? hy0)
        have hz'0 := ReachR.inner rr rn cR hir 0 y0 br hr0 hrn hrnl hbr
        simp only [beq_self_eq_true, ↓reduceIte] at hz'0
        refine Or.inl ⟨hz'm, hz'l, hz'r, _, br, hz'0,
          by rw [ite_zero_eq cR lo hcR0]; exact Nat.le_refl _, ?_⟩
        refine isNext_hiLE2 _ _ hir hi 0 cR br b
          (childBounds_isNext _ _ (KNode.liveAt_order rn t) _ _ hbr).2
          (childBounds_isNext _ hi hms _ _ hb).2 (Or.inl hhi) (fun r' hr' => (hrr' r' hr').2) ?_
        intro r' hr' hlt
        rcases hmlater r' hr' with h3 | ⟨_, h3 | h3⟩
        · have := (hlr r' (by rw [hlL]; exact h3)).2
          simp only [UpperBound] at this; omega
        · have hg := live_tail_gt rn (0, y0) r' hy0 h3
          exact ⟨r', by rw [hrL]; exact List.mem_of_mem_tail h3, hg, Nat.le_refl _⟩
        · omega
  · intro z lo hi m c z' _ hG hm hml' hcz
    rcases hG with ⟨hzm, hzl, hzr, lo0, hi0, hz0, _, _⟩ | ⟨hzm, lol, hir, hl0, hr0, _, _, _, _⟩
    · have hzp : z ≠ p := by intro h; rw [h, hN'p] at hm; cases hm; rw [hpl'] at hml'; cases hml'
      have hm0 : N z = some m := by rw [← hother z hzp hzl hzr hzm]; exact hm
      obtain ⟨hz'l, hz'r, hz'm⟩ := hchild z c z' (reachR_tReach N t r z lo0 hi0 hz0) ⟨m, hm0, hcz⟩ hzp
      exact Or.inl ⟨hz'm, hz'l, hz'r, 0, none, ReachR.seg z m lo0 hi0 c z' hz0 hm0 hml' hcz,
        Nat.le_refl _, HiLE.refl _⟩
    · rw [hzm, hN'm1] at hm; cases hm
      have hlnl : ln.leaf = true := by rw [← hml]; exact hml'
      have hrnl : rn.leaf = true := by rw [hrl]; exact hlnl
      have hin : inner = false := by rw [hinner, hlnl]; rfl
      rcases mem_mergeList inner cR ln.live rn.live c z' (hmn c z' hcz) with h1 | h1 | ⟨c0, h1, h2⟩
      · obtain ⟨hz'l, hz'r, hz'm⟩ := hlchild c z' h1
        exact Or.inl ⟨hz'm, hz'l, hz'r, 0, none,
          ReachR.seg l ln lol (some cR) c z' hl0 hln hlnl (by rw [hlL]; exact h1), Nat.le_refl _,
          HiLE.refl _⟩
      · obtain ⟨hz'l, hz'r, hz'm⟩ := hrchild c z' (List.mem_of_mem_tail h1)
        exact Or.inl ⟨hz'm, hz'l, hz'r, 0, none,
          ReachR.seg rr rn cR hir c z' hr0 hrn hrnl (by rw [hrL]; exact List.mem_of_mem_tail h1),
          Nat.le_refl _, HiLE.refl _⟩
      · rw [hin] at h2; simp only [Bool.false_eq_true, ↓reduceIte] at h2
        subst h2
        have hmem : (c, z') ∈ rn.live := List.mem_of_mem_head? h1
        obtain ⟨hz'l, hz'r, hz'm⟩ := hrchild c z' hmem
        exact Or.inl ⟨hz'm, hz'l, hz'r, 0, none,
          ReachR.seg rr rn cR hir c z' hr0 hrn hrnl (by rw [hrL]; exact hmem), Nat.le_refl _,
          HiLE.refl _⟩
  · intro z lo hi m _ hG hm
    rcases hG with ⟨hzm, hzl, hzr, lo0, hi0, hz0, hlo, hhi⟩ |
      ⟨hzm, lol, hir, hl0, hr0, hlo, hlolt, hiru, hhi⟩
    · by_cases hzp : z = p
      · rw [hzp, hN'p] at hm; cases hm
        rw [hzp] at hz0
        refine nodeRange_sub pn pn' t lo0 lo hi0 hi (hR p lo0 hi0 pn hz0 hpn) (by rw [hpl', hpl]) ?_
          hlo hhi
        intro q hq
        rcases hpn' q.1 q.2 hq with ⟨h1, _⟩ | ⟨h1, _, _⟩
        · exact ⟨(cL, l), hl, h1.symm⟩
        · exact ⟨q, h1, rfl⟩
      · have hm0 : N z = some m := by rw [← hother z hzp hzl hzr hzm]; exact hm
        exact nodeRange_wider m t lo0 lo hi0 hi (hR z lo0 hi0 m hz0 hm0) hlo hhi
    · rw [hzm, hN'm1] at hm; cases hm
      have hlr := hR l lol (some cR) ln hl0 hln
      have hrr' := hR rr cR hir rn hr0 hrn
      have hB := hBhi hir hi hiru hhi
      intro q hq
      rw [hml]
      rcases mem_mergeList inner cR ln.live rn.live q.1 q.2 (hmn q.1 q.2 hq) with h1 | h1 | ⟨c0, h1, h2⟩
      · obtain ⟨h3, h4⟩ := hlr q (by rw [hlL]; exact h1)
        refine ⟨?_, ?_⟩
        · cases hlnl : ln.leaf with
          | true => simp only [hlnl, ↓reduceIte] at h3 ⊢; omega
          | false => simp only [hlnl, Bool.false_eq_true, ↓reduceIte] at h3 ⊢; omega
        · simp only [UpperBound] at h4
          exact upperBound_of_hiLE (some cR) hi q.1 hB h4
      · have hq' : q ∈ rn.liveAt t := by rw [hrL]; exact List.mem_of_mem_tail h1
        obtain ⟨h3, h4⟩ := hrr' q hq'
        refine ⟨?_, upperBound_of_hiLE hir hi q.1 hhi h4⟩
        rw [hrl] at h3
        cases hlnl : ln.leaf with
        | true => simp only [hlnl, ↓reduceIte] at h3 ⊢; omega
        | false =>
          simp only [hlnl, Bool.false_eq_true, ↓reduceIte] at h3 ⊢
          have hin : inner = true := by rw [hinner, hlnl]; rfl
          obtain ⟨y0, hy0⟩ := hhead hin
          have hgt := live_tail_gt rn (0, y0) q hy0 h1
          simp only at hgt
          omega
      · have hmem : (c0, q.2) ∈ rn.live := List.mem_of_mem_head? h1
        obtain ⟨h3, h4⟩ := hrr' (c0, q.2) (by rw [hrL]; exact hmem)
        rw [hrl] at h3
        cases hlnl : ln.leaf with
        | true =>
          have hin : inner = false := by rw [hinner, hlnl]; rfl
          rw [hin] at h2; simp only [Bool.false_eq_true, ↓reduceIte] at h2
          simp only [hlnl, ↓reduceIte] at h3 ⊢
          rw [h2]
          exact ⟨by omega, upperBound_of_hiLE hir hi c0 hhi h4⟩
        | false =>
          have hin : inner = true := by rw [hinner, hlnl]; rfl
          rw [hin] at h2; simp only [↓reduceIte] at h2
          simp only [Bool.false_eq_true, ↓reduceIte]
          rw [h2]
          exact ⟨Or.inr (by omega), upperBound_of_hiLE hir hi cR hhi hiru⟩

/-- `isNext_hiLE_bound` with the old child's compare value c0 and the new one's
c apart, and the new high bound also an old later compare value. -/
theorem isNext_hiLE_bound2 (l0 l : List (Nat × NodeId)) (B : Nat) (hi : Option Nat) (c0 c : Nat)
    (b0 b : Option Nat) (h0 : IsNext l0 (some B) c0 b0) (h : IsNext l hi c b)
    (hl0B : ∀ r ∈ l0, r.1 < B)
    (hB : HiLE (some B) hi ∨ ∃ r ∈ l0, c0 < r.1 ∧ HiLE (some r.1) hi)
    (hlater : ∀ r ∈ l, c < r.1 → (r ∈ l0 ∧ c0 < r.1) ∨ B ≤ r.1) : HiLE b0 b := by
  have hb0 : ∃ x, b0 = some x ∧ x ≤ B := by
    rcases h0 with ⟨hb, _⟩ | ⟨r0, hr0, hb, _, _⟩
    · exact ⟨B, hb, Nat.le_refl _⟩
    · exact ⟨r0.1, hb, Nat.le_of_lt (hl0B r0 hr0)⟩
  obtain ⟨x, hx, hxB⟩ := hb0
  rw [hx]
  rcases h with ⟨hb, _⟩ | ⟨r, hr, hb, hlt, _⟩
  · rw [hb]
    rcases hB with hB | ⟨r, hr, hlt, hle⟩
    · have h1 : HiLE (some x) (some B) := ⟨x, rfl, hxB⟩
      exact HiLE.trans _ _ _ h1 hB
    · rcases h0 with ⟨_, hall⟩ | ⟨r0, _, hb0', _, hmin⟩
      · have := hall r hr; omega
      · rw [hx] at hb0'; cases hb0'
        have h1 : HiLE (some r0.1) (some r.1) := ⟨r0.1, rfl, hmin r hr hlt⟩
        exact HiLE.trans _ _ _ h1 hle
  · rw [hb]
    rcases hlater r hr hlt with ⟨hr0, hlt0⟩ | hBr
    · rcases h0 with ⟨_, hall⟩ | ⟨r0, _, hb0', _, hmin⟩
      · have := hall r hr0; omega
      · rw [hx] at hb0'; cases hb0'
        exact ⟨r0.1, rfl, hmin r hr0 hlt0⟩
    · exact ⟨x, rfl, Nat.le_trans hxB hBr⟩

/-- The walk's ranges after a merge into two nodes: the adjacent siblings l (cL)
and rr (cR) under p are replaced by m1, holding merged klongs below g, and m2,
holding those from g (g as the empty key in an inner node); p names m1 by cL and
m2 by g, and loses cR otherwise. -/
theorem rangeOrder_mergeTwo (N N' : NodeId → Option KNode) (t : Time) (r p l rr m1 m2 : NodeId)
    (pn ln rn pn' mn1 mn2 : KNode) (inner : Bool) (cL cR g : Nat)
    (hR : RangeOrder N t r) (hT : TreeOK N t r) (hp : TReach N t r p) (hpn : N p = some pn)
    (hpl : pn.leaf = false)
    (hl : (cL, l) ∈ pn.liveAt t) (hrr : (cR, rr) ∈ pn.liveAt t) (hcLR : cL < cR)
    (hadj : ∀ q ∈ pn.liveAt t, cL < q.1 → cR ≤ q.1)
    (hln : N l = some ln) (hrn : N rr = some rn)
    (hlt : ∀ s, Klong.time s ∈ ln.ks → s ≤ t) (hrt : ∀ s, Klong.time s ∈ rn.ks → s ≤ t)
    (hinner : inner = !ln.leaf) (hrl : rn.leaf = ln.leaf)
    (hhead : inner = true → ∃ y, rn.live.head? = some (0, y))
    (hm1 : N m1 = none) (hm1f : ∀ u c, TReach N t r u → ¬ TLink N t u c m1)
    (hm2 : N m2 = none) (hm2f : ∀ u c, TReach N t r u → ¬ TLink N t u c m2) (h12 : m1 ≠ m2)
    (hN'm1 : N' m1 = some mn1) (hml1 : mn1.leaf = ln.leaf)
    (hmn1 : ∀ c z, (c, z) ∈ mn1.liveAt t → (c, z) ∈ mergeList inner cR ln.live rn.live ∧ c < g)
    (hN'm2 : N' m2 = some mn2) (hml2 : mn2.leaf = ln.leaf)
    (hmn2 : ∀ c z, (c, z) ∈ mn2.liveAt t → ∃ c0, g ≤ c0 ∧
      (c0, z) ∈ mergeList inner cR ln.live rn.live ∧ c = (if c0 = g ∧ inner = true then 0 else c0))
    (hg : ∃ zg, (g, zg) ∈ mergeList inner cR ln.live rn.live)
    (hglow : ∃ c0 z0, (c0, z0) ∈ mergeList inner cR ln.live rn.live ∧ c0 < g)
    (hN'p : N' p = some pn') (hpl' : pn'.leaf = false)
    (hpn' : ∀ c z, (c, z) ∈ pn'.liveAt t →
      (c = cL ∧ z = m1) ∨ (c = g ∧ z = m2) ∨ ((c, z) ∈ pn.liveAt t ∧ c ≠ cL ∧ c ≠ cR))
    (hpn'g : (g, m2) ∈ pn'.liveAt t)
    (hother : ∀ y, y ≠ p → y ≠ l → y ≠ rr → y ≠ m1 → y ≠ m2 → N' y = N y) :
    RangeOrder N' t r := by
  have hlL : ln.liveAt t = ln.live := KNode.liveAt_of_times ln t hlt
  have hrL : rn.liveAt t = rn.live := KNode.liveAt_of_times rn t hrt
  have hlink_l : TLink N t p cL l := ⟨pn, hpn, hl⟩
  have hlink_r : TLink N t p cR rr := ⟨pn, hpn, hrr⟩
  have hlR : TReach N t r l := TReach.link hp hlink_l
  have hrR : TReach N t r rr := TReach.link hp hlink_r
  have hpl0 : p ≠ l := fun h => hT.no_self_link p cL hp (by rw [← h] at hlink_l; exact hlink_l)
  have hpr0 : p ≠ rr := fun h => hT.no_self_link p cR hp (by rw [← h] at hlink_r; exact hlink_r)
  have hm1p : p ≠ m1 := fun h => by rw [h, hm1] at hpn; cases hpn
  have hm1l : l ≠ m1 := fun h => by rw [h, hm1] at hln; cases hln
  have hm1r : rr ≠ m1 := fun h => by rw [h, hm1] at hrn; cases hrn
  have hm2p : p ≠ m2 := fun h => by rw [h, hm2] at hpn; cases hpn
  have hm2l : l ≠ m2 := fun h => by rw [h, hm2] at hln; cases hln
  have hm2r : rr ≠ m2 := fun h => by rw [h, hm2] at hrn; cases hrn
  have hrootm1 : r ≠ m1 := by
    intro h; obtain ⟨m, hm⟩ := hT.rootKey; rw [h, hm1] at hm; cases hm
  have hrootm2 : r ≠ m2 := by
    intro h; obtain ⟨m, hm⟩ := hT.rootKey; rw [h, hm2] at hm; cases hm
  have hrootl : r ≠ l := fun h => hT.rootFree p cL hp (h ▸ hlink_l)
  have hrootr : r ≠ rr := fun h => hT.rootFree p cR hp (h ▸ hlink_r)
  have hcR0 : cR ≠ 0 := by omega
  have hchild : ∀ u c z, TReach N t r u → TLink N t u c z → u ≠ p →
      z ≠ l ∧ z ≠ rr ∧ z ≠ m1 ∧ z ≠ m2 := by
    intro u c z hu hlk hup
    exact ⟨fun h => hup (hT.oneLink u c p cL l hu hp (h ▸ hlk) hlink_l).1,
      fun h => hup (hT.oneLink u c p cR rr hu hp (h ▸ hlk) hlink_r).1,
      fun h => hm1f u c hu (h ▸ hlk), fun h => hm2f u c hu (h ▸ hlk)⟩
  have hlchild : ∀ c z, (c, z) ∈ ln.live → z ≠ l ∧ z ≠ rr ∧ z ≠ m1 ∧ z ≠ m2 := fun c z h =>
    hchild l c z hlR ⟨ln, hln, by rw [hlL]; exact h⟩ hpl0.symm
  have hrchild : ∀ c z, (c, z) ∈ rn.live → z ≠ l ∧ z ≠ rr ∧ z ≠ m1 ∧ z ≠ m2 := fun c z h =>
    hchild rr c z hrR ⟨rn, hrn, by rw [hrL]; exact h⟩ hpr0.symm
  have hbl : ∀ hi0, ((cL, l), some cR) ∈ childBounds (pn.liveAt t) hi0 := by
    intro hi0
    apply childBounds_of_isNext _ hi0 (KNode.liveAt_order pn t) _ _ hl
    right
    exact ⟨(cR, rr), hrr, rfl, hcLR, fun r' hr' hlt => hadj r' hr' hlt⟩
  -- where a merged klong comes from
  have hsrc : ∀ c z, (c, z) ∈ mergeList inner cR ln.live rn.live →
      (c, z) ∈ ln.live ∨ ((c, z) ∈ rn.live ∧ (inner = true → 0 < c)) ∨
      (inner = true ∧ c = cR ∧ rn.live.head? = some (0, z)) := by
    intro c z h
    rcases mem_mergeList inner cR ln.live rn.live c z h with h1 | h1 | ⟨c0, h1, h2⟩
    · exact Or.inl h1
    · refine Or.inr (Or.inl ⟨List.mem_of_mem_tail h1, fun hin => ?_⟩)
      obtain ⟨y0, hy0⟩ := hhead hin
      have := live_tail_gt rn (0, y0) (c, z) hy0 h1
      simpa using this
    · cases hin : inner with
      | true =>
        rw [hin] at h2; simp only [↓reduceIte] at h2
        obtain ⟨y0, hy0⟩ := hhead hin
        rw [hy0] at h1
        simp only [Option.some.injEq, Prod.mk.injEq] at h1
        obtain ⟨h3, h4⟩ := h1
        refine Or.inr (Or.inr ⟨rfl, h2, ?_⟩)
        rw [hy0, h4]
      | false =>
        rw [hin] at h2; simp only [Bool.false_eq_true, ↓reduceIte] at h2
        subst h2
        exact Or.inr (Or.inl ⟨List.mem_of_mem_head? h1, fun h => by cases h⟩)
  -- the ranges of l and rr
  let C : Nat → Option Nat → Prop := fun lol hir =>
    ReachR N t r l lol (some cR) ∧ ReachR N t r rr cR hir ∧ lol < cR ∧ UpperBound hir cR
  -- the compare values of the merged klongs in the ranges of l and rr
  have hecv : ∀ lol hir, C lol hir → ∀ c z, (c, z) ∈ mergeList inner cR ln.live rn.live →
      UpperBound hir c ∧ (if ln.leaf then lol ≤ c else c = 0 ∨ lol < c) := by
    intro lol hir hC c z h
    obtain ⟨hl0, hr0, hlolt, hiru⟩ := hC
    rcases hsrc c z h with h1 | ⟨h1, h2⟩ | ⟨h1, h2, _⟩
    · obtain ⟨h3, h4⟩ := hR l lol (some cR) ln hl0 hln (c, z) (by rw [hlL]; exact h1)
      refine ⟨?_, h3⟩
      simp only [UpperBound] at h4
      cases hir with
      | none => trivial
      | some h' => simp only [UpperBound] at hiru ⊢; omega
    · obtain ⟨h3, h4⟩ := hR rr cR hir rn hr0 hrn (c, z) (by rw [hrL]; exact h1)
      refine ⟨h4, ?_⟩
      rw [hrl] at h3
      cases hlf : ln.leaf with
      | true => simp only [hlf, ↓reduceIte] at h3 ⊢; omega
      | false =>
        simp only [hlf, Bool.false_eq_true, ↓reduceIte] at h3 ⊢
        have hin : inner = true := by rw [hinner, hlf]; rfl
        have := h2 hin
        omega
    · rw [h2]
      refine ⟨hiru, ?_⟩
      have hlf : ln.leaf = false := by rw [hinner] at h1; simpa using h1
      simp only [hlf, Bool.false_eq_true, ↓reduceIte]
      omega
  let G : NodeId → Nat → Option Nat → Prop := fun z lo hi =>
    (z ≠ m1 ∧ z ≠ m2 ∧ z ≠ l ∧ z ≠ rr ∧ ∃ lo0 hi0, ReachR N t r z lo0 hi0 ∧ lo ≤ lo0 ∧ HiLE hi0 hi) ∨
    (z = m1 ∧ hi = some g ∧ ∃ lol hir, C lol hir ∧ lo ≤ lol) ∨
    (z = m2 ∧ lo = g ∧ ∃ lol hir, C lol hir ∧ HiLE hir hi)
  have hg0 : 0 < g := by obtain ⟨c0, _, _, h⟩ := hglow; omega
  -- the facts of g below a range of p
  have hgfacts : ∀ lo0 hi0, ReachR N t r p lo0 hi0 → ∀ b0,
      ((cR, rr), b0) ∈ childBounds (pn.liveAt t) hi0 →
      C (if cL == 0 then lo0 else cL) b0 ∧ cL < g ∧ lo0 < g ∧ UpperBound b0 g ∧
        UpperBound hi0 g ∧ (∀ q ∈ pn.liveAt t, cR < q.1 → g < q.1) := by
    intro lo0 hi0 hz0 b0 hb0
    have hpr := hR p lo0 hi0 pn hz0 hpn
    have hcRl := (hpr (cR, rr) hrr).1
    simp only [hpl, Bool.false_eq_true, ↓reduceIte] at hcRl
    have hcLl := (hpr (cL, l) hl).1
    simp only [hpl, Bool.false_eq_true, ↓reduceIte] at hcLl
    have hrr0 := ReachR.inner p pn lo0 hi0 cR rr b0 hz0 hpn hpl hb0
    rw [ite_zero_eq cR lo0 hcR0] at hrr0
    have hnb0 := (childBounds_isNext _ hi0 (KNode.liveAt_order pn t) _ _ hb0).2
    have hb0u : UpperBound b0 cR := by
      rcases hnb0 with ⟨hb', _⟩ | ⟨r', _, hb', hlt', _⟩
      · rw [hb']; exact (hpr (cR, rr) hrr).2
      · rw [hb']; simp only [UpperBound]; exact hlt'
    have hlol : (if cL == 0 then lo0 else cL) < cR := by
      by_cases hk : cL = 0
      · rw [hk]; simp only [beq_self_eq_true, ↓reduceIte]; omega
      · rw [ite_zero_eq cL lo0 hk]; exact hcLR
    have hC : C (if cL == 0 then lo0 else cL) b0 :=
      ⟨ReachR.inner p pn lo0 hi0 cL l (some cR) hz0 hpn hpl (hbl hi0), hrr0, hlol, hb0u⟩
    obtain ⟨zg, hgz⟩ := hg
    obtain ⟨c0, z0, hc0z, hc0g⟩ := hglow
    obtain ⟨hgu, hgl⟩ := hecv _ _ hC g zg hgz
    obtain ⟨_, hc0l⟩ := hecv _ _ hC c0 z0 hc0z
    have hlolg : (if cL == 0 then lo0 else cL) < g := by
      cases hlf : ln.leaf with
      | true => simp only [hlf, ↓reduceIte] at hc0l; omega
      | false => simp only [hlf, Bool.false_eq_true, ↓reduceIte] at hgl; omega
    have hcLg : cL < g := by
      by_cases hk : cL = 0
      · omega
      · rw [ite_zero_eq cL lo0 hk] at hlolg; exact hlolg
    have hlo0g : lo0 < g := by
      by_cases hk : cL = 0
      · rw [hk] at hlolg; simp only [beq_self_eq_true, ↓reduceIte] at hlolg; exact hlolg
      · omega
    have hhi0g : UpperBound hi0 g := by
      rcases hnb0 with ⟨hb', _⟩ | ⟨r', hr', hb', _, _⟩
      · rw [← hb']; exact hgu
      · rw [hb'] at hgu
        have := (hpr r' hr').2
        cases hi0 with
        | none => trivial
        | some h0 => simp only [UpperBound] at this hgu ⊢; omega
    refine ⟨hC, hcLg, hlo0g, hgu, hhi0g, ?_⟩
    intro q hq hlt
    rcases hnb0 with ⟨_, hall⟩ | ⟨r', _, hb', _, hmin⟩
    · have := hall q hq; omega
    · rw [hb'] at hgu; simp only [UpperBound] at hgu
      have := hmin q hq hlt; omega
  apply rangeOrder_of_good N' t r G
  · exact Or.inl ⟨hrootm1, hrootm2, hrootl, hrootr, 0, none, ReachR.root, Nat.le_refl _, HiLE.refl _⟩
  · intro z lo hi m c z' b _ hG hm hml' hb
    have hcz := childBounds_fst _ _ _ _ hb
    have hms := KNode.liveAt_order m t
    rcases hG with ⟨hzm1, hzm2, hzl, hzr, lo0, hi0, hz0, hlo, hhi⟩ | ⟨hzm, hhs, lol, hir, hC, hlo⟩ |
      ⟨hzm, hls, lol, hir, hC, hhi⟩
    · by_cases hzp : z = p
      · rw [hzp, hN'p] at hm; cases hm
        rw [hzp] at hz0
        have hpr := hR p lo0 hi0 pn hz0 hpn
        obtain ⟨b0, hb0⟩ := childBounds_exists (pn.liveAt t) hi0 (cR, rr) hrr
        obtain ⟨hC, hcLg, _, _, _, habove⟩ := hgfacts lo0 hi0 hz0 b0 hb0
        rcases hpn' c z' hcz with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
        · rw [h1, h2] at hb ⊢
          have hbF : b = some g := by
            refine isNext_unique _ hi cL b (some g) (childBounds_isNext _ hi hms _ _ hb).2 ?_
            right
            refine ⟨(g, m2), hpn'g, rfl, hcLg, ?_⟩
            intro r' hr' hlt
            rcases hpn' r'.1 r'.2 hr' with ⟨h4, _⟩ | ⟨h4, _⟩ | ⟨h4, h5, h6⟩
            · omega
            · simp only; omega
            · have := hadj r' h4 hlt
              have := habove r' h4 (by omega)
              simp only; omega
          refine Or.inr (Or.inl ⟨rfl, hbF, _, b0, hC, ?_⟩)
          by_cases hk : cL = 0
          · rw [hk]; simp only [beq_self_eq_true, ↓reduceIte]; exact hlo
          · have e1 := ite_zero_eq cL lo hk; have e2 := ite_zero_eq cL lo0 hk; omega
        · rw [h1, h2] at hb ⊢
          refine Or.inr (Or.inr ⟨rfl, ite_zero_eq g lo (by omega), _, b0, hC, ?_⟩)
          refine isNext_hiLE2 _ _ hi0 hi cR g b0 b
            (childBounds_isNext _ hi0 (KNode.liveAt_order pn t) _ _ hb0).2
            (childBounds_isNext _ hi hms _ _ hb).2 (Or.inl hhi) (fun r' hr' => (hpr r' hr').2) ?_
          intro r' hr' hlt
          rcases hpn' r'.1 r'.2 hr' with ⟨h4, _⟩ | ⟨h4, _⟩ | ⟨h4, h5, h6⟩
          · omega
          · omega
          · have := hadj r' h4 (by omega)
            exact ⟨r', h4, by omega, Nat.le_refl _⟩
        · have hz'l : z' ≠ l := fun h => h2 (hT.oneLink p c p cL l hp hp ⟨pn, hpn, h ▸ h1⟩ hlink_l).2
          have hz'r : z' ≠ rr := fun h => h3 (hT.oneLink p c p cR rr hp hp ⟨pn, hpn, h ▸ h1⟩ hlink_r).2
          have hz'm1 : z' ≠ m1 := fun h => hm1f p c hp ⟨pn, hpn, h ▸ h1⟩
          have hz'm2 : z' ≠ m2 := fun h => hm2f p c hp ⟨pn, hpn, h ▸ h1⟩
          have hlat : ∀ r' ∈ pn'.liveAt t, c < r'.1 →
              ∃ r0 ∈ pn.liveAt t, c < r0.1 ∧ r0.1 ≤ r'.1 := by
            intro r' hr' hlt
            rcases hpn' r'.1 r'.2 hr' with ⟨h7, _⟩ | ⟨h7, _⟩ | ⟨h7, _, _⟩
            · exact ⟨(cL, l), hl, by simp only; omega, by simp only; omega⟩
            · rcases Nat.lt_or_ge c cL with hcc | hcc
              · exact ⟨(cL, l), hl, hcc, by simp only; omega⟩
              · have := hadj (c, z') h1 (by simp only; omega)
                have := habove (c, z') h1 (by simp only at this ⊢; omega)
                simp only at this; omega
            · exact ⟨r', h7, hlt, Nat.le_refl _⟩
          obtain ⟨lo1, hi1, h4, h5, h6⟩ := old_child_step N t r hR p pn lo0 lo hi0 hi hz0 hpn hpl hlo
            hhi _ hms c z' z' b h1 hb hlat
          exact Or.inl ⟨hz'm1, hz'm2, hz'l, hz'r, lo1, hi1, h4, h5, h6⟩
      · have hm0 : N z = some m := by rw [← hother z hzp hzl hzr hzm1 hzm2]; exact hm
        obtain ⟨hz'l, hz'r, hz'm1, hz'm2⟩ := hchild z c z' (reachR_tReach N t r z lo0 hi0 hz0)
          ⟨m, hm0, hcz⟩ hzp
        obtain ⟨lo1, hi1, h4, h5, h6⟩ := old_child_step N t r hR z m lo0 lo hi0 hi hz0 hm0 hml' hlo
          hhi _ hms c z' z' b hcz hb (fun r' hr' hlt => ⟨r', hr', hlt, Nat.le_refl _⟩)
        exact Or.inl ⟨hz'm1, hz'm2, hz'l, hz'r, lo1, hi1, h4, h5, h6⟩
    · -- a child of m1
      rw [hzm, hN'm1] at hm; cases hm
      rw [hhs] at hb
      obtain ⟨hl0, hr0, hlolt, hiru⟩ := hC
      have hlnl : ln.leaf = false := by rw [← hml1]; exact hml'
      have hrnl : rn.leaf = false := by rw [hrl]; exact hlnl
      have hin : inner = true := by rw [hinner, hlnl]; rfl
      have hlr := hR l lol (some cR) ln hl0 hln
      have hrr' := hR rr cR hir rn hr0 hrn
      obtain ⟨hce, hcg⟩ := hmn1 c z' hcz
      obtain ⟨zg, hgz⟩ := hg
      rcases hsrc c z' hce with h1 | ⟨h1, h2⟩ | ⟨_, h2, h3⟩
      · have h1' : (c, z') ∈ ln.liveAt t := by rw [hlL]; exact h1
        obtain ⟨bl, hbl0⟩ := childBounds_exists (ln.liveAt t) (some cR) (c, z') h1'
        obtain ⟨hz'l, hz'r, hz'm1, hz'm2⟩ := hlchild c z' h1
        refine Or.inl ⟨hz'm1, hz'm2, hz'l, hz'r, _, bl,
          ReachR.inner l ln lol (some cR) c z' bl hl0 hln hlnl hbl0, ?_, ?_⟩
        · by_cases hk : c = 0
          · rw [hk]; simp only [beq_self_eq_true, ↓reduceIte]; exact hlo
          · have e1 := ite_zero_eq c lo hk; have e2 := ite_zero_eq c lol hk; omega
        · refine isNext_hiLE_bound2 _ _ cR (some g) c c bl b
            (childBounds_isNext _ _ (KNode.liveAt_order ln t) _ _ hbl0).2
            (childBounds_isNext _ _ hms _ _ hb).2 (fun r' hr' => by
              have := (hlr r' hr').2; simp only [UpperBound] at this; exact this) ?_ ?_
          · rcases Nat.lt_or_ge g cR with hgc | hgc
            · right
              rcases hsrc g zg hgz with h4 | ⟨h4, h5⟩ | ⟨_, h5, _⟩
              · exact ⟨(g, zg), by rw [hlL]; exact h4, hcg, HiLE.refl _⟩
              · have := (hrr' (g, zg) (by rw [hrL]; exact h4)).1
                simp only [hrnl, Bool.false_eq_true, ↓reduceIte] at this
                have := h5 hin; omega
              · omega
            · left; exact ⟨cR, rfl, hgc⟩
          · intro r' hr' hlt
            obtain ⟨hre, _⟩ := hmn1 r'.1 r'.2 hr'
            rcases hsrc r'.1 r'.2 hre with h4 | ⟨h4, h5⟩ | ⟨_, h5, _⟩
            · left; exact ⟨by rw [hlL]; exact h4, hlt⟩
            · right
              have := (hrr' r' (by rw [hrL]; exact h4)).1
              simp only [hrnl, Bool.false_eq_true, ↓reduceIte] at this
              have := h5 hin; omega
            · right; omega
      · have hc0 := h2 hin
        have h1' : (c, z') ∈ rn.liveAt t := by rw [hrL]; exact h1
        have hcR : cR < c := by
          have := (hrr' (c, z') h1').1
          simp only [hrnl, Bool.false_eq_true, ↓reduceIte] at this; omega
        obtain ⟨br, hbr⟩ := childBounds_exists (rn.liveAt t) hir (c, z') h1'
        obtain ⟨hz'l, hz'r, hz'm1, hz'm2⟩ := hrchild c z' h1
        have hz'0 := ReachR.inner rr rn cR hir c z' br hr0 hrn hrnl hbr
        rw [ite_zero_eq c cR (by omega)] at hz'0
        refine Or.inl ⟨hz'm1, hz'm2, hz'l, hz'r, _, br, hz'0,
          by rw [ite_zero_eq c lo (by omega)]; exact Nat.le_refl _, ?_⟩
        refine isNext_hiLE2 _ _ hir (some g) c c br b
          (childBounds_isNext _ _ (KNode.liveAt_order rn t) _ _ hbr).2
          (childBounds_isNext _ _ hms _ _ hb).2 ?_ (fun r' hr' => (hrr' r' hr').2) ?_
        · right
          rcases hsrc g zg hgz with h4 | ⟨h4, h5⟩ | ⟨_, h5, _⟩
          · have := (hlr (g, zg) (by rw [hlL]; exact h4)).2
            simp only [UpperBound] at this; omega
          · exact ⟨(g, zg), by rw [hrL]; exact h4, hcg, HiLE.refl _⟩
          · omega
        · intro r' hr' hlt
          obtain ⟨hre, _⟩ := hmn1 r'.1 r'.2 hr'
          rcases hsrc r'.1 r'.2 hre with h4 | ⟨h4, _⟩ | ⟨_, h5, _⟩
          · have := (hlr r' (by rw [hlL]; exact h4)).2
            simp only [UpperBound] at this; omega
          · exact ⟨r', by rw [hrL]; exact h4, hlt, Nat.le_refl _⟩
          · omega
      · rw [h2] at hb hcg ⊢
        have hy0' : (0, z') ∈ rn.liveAt t := by rw [hrL]; exact List.mem_of_mem_head? h3
        obtain ⟨br, hbr⟩ := childBounds_exists (rn.liveAt t) hir (0, z') hy0'
        obtain ⟨hz'l, hz'r, hz'm1, hz'm2⟩ := hrchild 0 z' (List.mem_of_mem_head? h3)
        have hz'0 := ReachR.inner rr rn cR hir 0 z' br hr0 hrn hrnl hbr
        simp only [beq_self_eq_true, ↓reduceIte] at hz'0
        refine Or.inl ⟨hz'm1, hz'm2, hz'l, hz'r, _, br, hz'0,
          by rw [ite_zero_eq cR lo hcR0]; exact Nat.le_refl _, ?_⟩
        refine isNext_hiLE2 _ _ hir (some g) 0 cR br b
          (childBounds_isNext _ _ (KNode.liveAt_order rn t) _ _ hbr).2
          (childBounds_isNext _ _ hms _ _ hb).2 ?_ (fun r' hr' => (hrr' r' hr').2) ?_
        · right
          rcases hsrc g zg hgz with h4 | ⟨h4, h5⟩ | ⟨_, h5, _⟩
          · have := (hlr (g, zg) (by rw [hlL]; exact h4)).2
            simp only [UpperBound] at this; omega
          · exact ⟨(g, zg), by rw [hrL]; exact h4, h5 hin, HiLE.refl _⟩
          · omega
        · intro r' hr' hlt
          obtain ⟨hre, _⟩ := hmn1 r'.1 r'.2 hr'
          rcases hsrc r'.1 r'.2 hre with h4 | ⟨h4, h5⟩ | ⟨_, h5, _⟩
          · have := (hlr r' (by rw [hlL]; exact h4)).2
            simp only [UpperBound] at this; omega
          · exact ⟨r', by rw [hrL]; exact h4, h5 hin, Nat.le_refl _⟩
          · omega
    · -- a child of m2
      rw [hzm, hN'm2] at hm; cases hm
      rw [hls]
      obtain ⟨hl0, hr0, hlolt, hiru⟩ := hC
      have hlnl : ln.leaf = false := by rw [← hml2]; exact hml'
      have hrnl : rn.leaf = false := by rw [hrl]; exact hlnl
      have hin : inner = true := by rw [hinner, hlnl]; rfl
      have hlr := hR l lol (some cR) ln hl0 hln
      have hrr' := hR rr cR hir rn hr0 hrn
      have hcRhi : HiLE (some cR) hi := by
        cases hi with
        | none => trivial
        | some h =>
          obtain ⟨b0, hb0, hle⟩ := hhi
          subst hb0
          simp only [UpperBound] at hiru
          exact ⟨cR, rfl, by omega⟩
      obtain ⟨c0, hgc0, hce, hceq⟩ := hmn2 c z' hcz
      simp only [hin, and_true] at hceq
      -- the new low bound of the child is c0
      have hlo' : (if c == 0 then g else c) = c0 := by
        by_cases hcs : c0 = g
        · simp only [hcs, ↓reduceIte] at hceq; rw [hceq]; simp [hcs]
        · simp only [hcs, ↓reduceIte] at hceq; rw [hceq, ite_zero_eq c0 g (by omega)]
      -- a later klong of m2 after c is one of compare value above c0
      have hm2later : ∀ r' ∈ mn2.liveAt t, c < r'.1 →
          c0 < r'.1 ∧ (r'.1, r'.2) ∈ mergeList inner cR ln.live rn.live := by
        intro r' hr' hlt
        obtain ⟨c0', hgc0', hce', hceq'⟩ := hmn2 r'.1 r'.2 hr'
        simp only [hin, and_true] at hceq'
        by_cases hcs' : c0' = g
        · simp only [hcs', ↓reduceIte] at hceq'; omega
        · simp only [hcs', ↓reduceIte] at hceq'
          rw [hceq']
          refine ⟨?_, hce'⟩
          by_cases hcs : c0 = g
          · omega
          · simp only [hcs, ↓reduceIte] at hceq; omega
      rcases hsrc c0 z' hce with h1 | ⟨h1, h2⟩ | ⟨_, h2, h3⟩
      · have h1' : (c0, z') ∈ ln.liveAt t := by rw [hlL]; exact h1
        obtain ⟨bl, hbl0⟩ := childBounds_exists (ln.liveAt t) (some cR) (c0, z') h1'
        obtain ⟨hz'l, hz'r, hz'm1, hz'm2⟩ := hlchild c0 z' h1
        have hz'0 := ReachR.inner l ln lol (some cR) c0 z' bl hl0 hln hlnl hbl0
        rw [ite_zero_eq c0 lol (by omega)] at hz'0
        refine Or.inl ⟨hz'm1, hz'm2, hz'l, hz'r, _, bl, hz'0, by rw [hlo']; exact Nat.le_refl _, ?_⟩
        refine isNext_hiLE_bound2 _ _ cR hi c0 c bl b
          (childBounds_isNext _ _ (KNode.liveAt_order ln t) _ _ hbl0).2
          (childBounds_isNext _ _ hms _ _ hb).2 (fun r' hr' => by
            have := (hlr r' hr').2; simp only [UpperBound] at this; exact this) (Or.inl hcRhi) ?_
        intro r' hr' hlt
        obtain ⟨h4, h5⟩ := hm2later r' hr' hlt
        rcases hsrc r'.1 r'.2 h5 with h6 | ⟨h6, h7⟩ | ⟨_, h7, _⟩
        · left; exact ⟨by rw [hlL]; exact h6, h4⟩
        · right
          have := (hrr' r' (by rw [hrL]; exact h6)).1
          simp only [hrnl, Bool.false_eq_true, ↓reduceIte] at this
          have := h7 hin; omega
        · right; omega
      · have hc0' := h2 hin
        have h1' : (c0, z') ∈ rn.liveAt t := by rw [hrL]; exact h1
        have hcR : cR < c0 := by
          have := (hrr' (c0, z') h1').1
          simp only [hrnl, Bool.false_eq_true, ↓reduceIte] at this; omega
        obtain ⟨br, hbr⟩ := childBounds_exists (rn.liveAt t) hir (c0, z') h1'
        obtain ⟨hz'l, hz'r, hz'm1, hz'm2⟩ := hrchild c0 z' h1
        have hz'0 := ReachR.inner rr rn cR hir c0 z' br hr0 hrn hrnl hbr
        rw [ite_zero_eq c0 cR (by omega)] at hz'0
        refine Or.inl ⟨hz'm1, hz'm2, hz'l, hz'r, _, br, hz'0, by rw [hlo']; exact Nat.le_refl _, ?_⟩
        refine isNext_hiLE2 _ _ hir hi c0 c br b
          (childBounds_isNext _ _ (KNode.liveAt_order rn t) _ _ hbr).2
          (childBounds_isNext _ _ hms _ _ hb).2 (Or.inl hhi) (fun r' hr' => (hrr' r' hr').2) ?_
        intro r' hr' hlt
        obtain ⟨h4, h5⟩ := hm2later r' hr' hlt
        rcases hsrc r'.1 r'.2 h5 with h6 | ⟨h6, _⟩ | ⟨_, h7, _⟩
        · have := (hlr r' (by rw [hlL]; exact h6)).2
          simp only [UpperBound] at this; omega
        · exact ⟨r', by rw [hrL]; exact h6, h4, Nat.le_refl _⟩
        · omega
      · have hy0' : (0, z') ∈ rn.liveAt t := by rw [hrL]; exact List.mem_of_mem_head? h3
        obtain ⟨br, hbr⟩ := childBounds_exists (rn.liveAt t) hir (0, z') hy0'
        obtain ⟨hz'l, hz'r, hz'm1, hz'm2⟩ := hrchild 0 z' (List.mem_of_mem_head? h3)
        have hz'0 := ReachR.inner rr rn cR hir 0 z' br hr0 hrn hrnl hbr
        simp only [beq_self_eq_true, ↓reduceIte] at hz'0
        refine Or.inl ⟨hz'm1, hz'm2, hz'l, hz'r, _, br, hz'0, by rw [hlo', h2]; exact Nat.le_refl _, ?_⟩
        refine isNext_hiLE2 _ _ hir hi 0 c br b
          (childBounds_isNext _ _ (KNode.liveAt_order rn t) _ _ hbr).2
          (childBounds_isNext _ _ hms _ _ hb).2 (Or.inl hhi) (fun r' hr' => (hrr' r' hr').2) ?_
        intro r' hr' hlt
        obtain ⟨h4, h5⟩ := hm2later r' hr' hlt
        rcases hsrc r'.1 r'.2 h5 with h6 | ⟨h6, h7⟩ | ⟨_, h7, _⟩
        · have := (hlr r' (by rw [hlL]; exact h6)).2
          simp only [UpperBound] at this; omega
        · exact ⟨r', by rw [hrL]; exact h6, h7 hin, Nat.le_refl _⟩
        · omega
  · intro z lo hi m c z' _ hG hm hml' hcz
    rcases hG with ⟨hzm1, hzm2, hzl, hzr, lo0, hi0, hz0, _, _⟩ | ⟨hzm, _, lol, hir, hC, _⟩ |
      ⟨hzm, _, lol, hir, hC, _⟩
    · have hzp : z ≠ p := by intro h; rw [h, hN'p] at hm; cases hm; rw [hpl'] at hml'; cases hml'
      have hm0 : N z = some m := by rw [← hother z hzp hzl hzr hzm1 hzm2]; exact hm
      obtain ⟨hz'l, hz'r, hz'm1, hz'm2⟩ := hchild z c z' (reachR_tReach N t r z lo0 hi0 hz0)
        ⟨m, hm0, hcz⟩ hzp
      exact Or.inl ⟨hz'm1, hz'm2, hz'l, hz'r, 0, none, ReachR.seg z m lo0 hi0 c z' hz0 hm0 hml' hcz,
        Nat.le_refl _, HiLE.refl _⟩
    · rw [hzm, hN'm1] at hm; cases hm
      obtain ⟨hl0, hr0, _, _⟩ := hC
      have hlnl : ln.leaf = true := by rw [← hml1]; exact hml'
      have hrnl : rn.leaf = true := by rw [hrl]; exact hlnl
      obtain ⟨hce, _⟩ := hmn1 c z' hcz
      rcases hsrc c z' hce with h1 | ⟨h1, _⟩ | ⟨h2, _, _⟩
      · obtain ⟨hz'l, hz'r, hz'm1, hz'm2⟩ := hlchild c z' h1
        exact Or.inl ⟨hz'm1, hz'm2, hz'l, hz'r, 0, none,
          ReachR.seg l ln lol (some cR) c z' hl0 hln hlnl (by rw [hlL]; exact h1), Nat.le_refl _,
          HiLE.refl _⟩
      · obtain ⟨hz'l, hz'r, hz'm1, hz'm2⟩ := hrchild c z' h1
        exact Or.inl ⟨hz'm1, hz'm2, hz'l, hz'r, 0, none,
          ReachR.seg rr rn cR hir c z' hr0 hrn hrnl (by rw [hrL]; exact h1), Nat.le_refl _,
          HiLE.refl _⟩
      · rw [hinner, hlnl] at h2; cases h2
    · rw [hzm, hN'm2] at hm; cases hm
      obtain ⟨hl0, hr0, _, _⟩ := hC
      have hlnl : ln.leaf = true := by rw [← hml2]; exact hml'
      have hrnl : rn.leaf = true := by rw [hrl]; exact hlnl
      obtain ⟨c0, _, hce, _⟩ := hmn2 c z' hcz
      rcases hsrc c0 z' hce with h1 | ⟨h1, _⟩ | ⟨h2, _, _⟩
      · obtain ⟨hz'l, hz'r, hz'm1, hz'm2⟩ := hlchild c0 z' h1
        exact Or.inl ⟨hz'm1, hz'm2, hz'l, hz'r, 0, none,
          ReachR.seg l ln lol (some cR) c0 z' hl0 hln hlnl (by rw [hlL]; exact h1), Nat.le_refl _,
          HiLE.refl _⟩
      · obtain ⟨hz'l, hz'r, hz'm1, hz'm2⟩ := hrchild c0 z' h1
        exact Or.inl ⟨hz'm1, hz'm2, hz'l, hz'r, 0, none,
          ReachR.seg rr rn cR hir c0 z' hr0 hrn hrnl (by rw [hrL]; exact h1), Nat.le_refl _,
          HiLE.refl _⟩
      · rw [hinner, hlnl] at h2; cases h2
  · intro z lo hi m _ hG hm
    rcases hG with ⟨hzm1, hzm2, hzl, hzr, lo0, hi0, hz0, hlo, hhi⟩ | ⟨hzm, hhs, lol, hir, hC, hlo⟩ |
      ⟨hzm, hls, lol, hir, hC, hhi⟩
    · by_cases hzp : z = p
      · rw [hzp, hN'p] at hm; cases hm
        rw [hzp] at hz0
        have hpr := hR p lo0 hi0 pn hz0 hpn
        obtain ⟨b0, hb0⟩ := childBounds_exists (pn.liveAt t) hi0 (cR, rr) hrr
        obtain ⟨_, _, hlo0g, _, hhi0g, _⟩ := hgfacts lo0 hi0 hz0 b0 hb0
        intro q hq
        simp only [hpl', Bool.false_eq_true, ↓reduceIte]
        rcases hpn' q.1 q.2 hq with ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h1, _, _⟩
        · obtain ⟨h3, h4⟩ := hpr (cL, l) hl
          simp only [hpl, Bool.false_eq_true, ↓reduceIte] at h3
          rw [h1]; exact ⟨by omega, upperBound_of_hiLE hi0 hi cL hhi h4⟩
        · rw [h1]; exact ⟨Or.inr (by omega), upperBound_of_hiLE hi0 hi g hhi hhi0g⟩
        · obtain ⟨h3, h4⟩ := hpr q h1
          simp only [hpl, Bool.false_eq_true, ↓reduceIte] at h3
          exact ⟨by omega, upperBound_of_hiLE hi0 hi q.1 hhi h4⟩
      · have hm0 : N z = some m := by rw [← hother z hzp hzl hzr hzm1 hzm2]; exact hm
        exact nodeRange_wider m t lo0 lo hi0 hi (hR z lo0 hi0 m hz0 hm0) hlo hhi
    · rw [hzm, hN'm1] at hm; cases hm
      rw [hhs]
      intro q hq
      obtain ⟨hce, hcg⟩ := hmn1 q.1 q.2 hq
      obtain ⟨_, h3⟩ := hecv lol hir hC q.1 q.2 hce
      rw [hml1]
      refine ⟨?_, by simp only [UpperBound]; exact hcg⟩
      cases hlf : ln.leaf with
      | true => simp only [hlf, ↓reduceIte] at h3 ⊢; omega
      | false => simp only [hlf, Bool.false_eq_true, ↓reduceIte] at h3 ⊢; omega
    · rw [hzm, hN'm2] at hm; cases hm
      rw [hls]
      intro q hq
      obtain ⟨c0, hgc0, hce, hceq⟩ := hmn2 q.1 q.2 hq
      obtain ⟨h3, _⟩ := hecv lol hir hC c0 q.2 hce
      have hup : UpperBound hi c0 := upperBound_of_hiLE hir hi c0 hhi h3
      rw [hml2]
      cases hlf : ln.leaf with
      | true =>
        have hin : inner = false := by rw [hinner, hlf]; rfl
        simp only [hin, Bool.false_eq_true, and_false, ↓reduceIte] at hceq
        simp only [↓reduceIte]
        rw [hceq]; exact ⟨hgc0, hup⟩
      | false =>
        have hin : inner = true := by rw [hinner, hlf]; rfl
        simp only [hin, and_true] at hceq
        simp only [Bool.false_eq_true, ↓reduceIte]
        by_cases hcs : c0 = g
        · simp only [hcs, ↓reduceIte] at hceq
          rw [hceq]
          refine ⟨Or.inl rfl, ?_⟩
          cases hi with
          | none => trivial
          | some h => simp only [UpperBound] at hup ⊢; omega
        · simp only [hcs, ↓reduceIte] at hceq
          rw [hceq]; exact ⟨Or.inr (by omega), hup⟩

end SIS.Tree
