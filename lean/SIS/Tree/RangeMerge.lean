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

end SIS.Tree
