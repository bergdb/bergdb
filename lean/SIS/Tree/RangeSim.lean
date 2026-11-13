import SIS.Tree.PutInvRange
import SIS.Tree.WriterTreeVisits

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! The walk's ranges after a change of the tree (bergdb 024-12, TP10): the
tools to prove that an operation keeps `RangeOrder`.

A child's range is its parent's klong to it (the parent's own low bound for the
empty key) up to the parent's next live compare value, or the parent's own high
bound after the last one (`IsNext`, `childBounds_isNext`). `RangeOrder` after a
change follows from a predicate on the nodes reached with a range that the root
meets, that every child step keeps and that gives each node's range
(`rangeOrder_of_good`). A node reached after with a range at least as wide as
one with which it, or the node it stands for, was reached before keeps its old
children with ranges at least as wide (`old_child_step`, `HiLE`). -/

/-! ## Bounds -/

/-- The upper bound hi0 is at most hi (none: no bound). -/
def HiLE (hi0 hi : Option Nat) : Prop :=
  match hi with
  | none => True
  | some b => ∃ b0, hi0 = some b0 ∧ b0 ≤ b

theorem HiLE.refl (h : Option Nat) : HiLE h h := by
  cases h with
  | none => trivial
  | some b => exact ⟨b, rfl, Nat.le_refl _⟩

theorem HiLE.none (h : Option Nat) : HiLE h none := trivial

theorem HiLE.trans (a b c : Option Nat) (h1 : HiLE a b) (h2 : HiLE b c) : HiLE a c := by
  cases c with
  | none => trivial
  | some c =>
    obtain ⟨b0, hb, hbc⟩ := h2
    subst hb
    obtain ⟨a0, ha, hab⟩ := h1
    exact ⟨a0, ha, Nat.le_trans hab hbc⟩

theorem upperBound_of_hiLE (hi0 hi : Option Nat) (c : Nat) (hh : HiLE hi0 hi)
    (hu : UpperBound hi0 c) : UpperBound hi c := by
  cases hi with
  | none => trivial
  | some b =>
    obtain ⟨b0, hb0, hle⟩ := hh
    subst hb0
    simp only [UpperBound] at hu ⊢
    omega

theorem hiLE_some_of_upper (hi : Option Nat) (c : Nat) (hu : UpperBound hi c) :
    HiLE (some c) hi := by
  cases hi with
  | none => trivial
  | some b => exact ⟨c, rfl, by simp only [UpperBound] at hu; omega⟩

/-- A node's range kept with a range at least as wide, its live compare values
among those of a node in range. -/
theorem nodeRange_sub (n0 n : KNode) (t lo0 lo : Nat) (hi0 hi : Option Nat)
    (h : NodeRange n0 t lo0 hi0) (hlf : n.leaf = n0.leaf)
    (hsub : ∀ q ∈ n.liveAt t, ∃ q0 ∈ n0.liveAt t, q0.1 = q.1)
    (hlo : lo ≤ lo0) (hhi : HiLE hi0 hi) : NodeRange n t lo hi := by
  intro q hq
  obtain ⟨q0, hq0, he⟩ := hsub q hq
  obtain ⟨h1, h2⟩ := h q0 hq0
  rw [he] at h1 h2
  refine ⟨?_, upperBound_of_hiLE hi0 hi q.1 hhi h2⟩
  rw [hlf]
  cases hl : n0.leaf with
  | true => simp only [hl, ↓reduceIte] at h1 ⊢; omega
  | false => simp only [hl, Bool.false_eq_true, ↓reduceIte] at h1 ⊢; omega

theorem nodeRange_wider (n : KNode) (t lo0 lo : Nat) (hi0 hi : Option Nat)
    (h : NodeRange n t lo0 hi0) (hlo : lo ≤ lo0) (hhi : HiLE hi0 hi) : NodeRange n t lo hi :=
  nodeRange_sub n n t lo0 lo hi0 hi h rfl (fun q hq => ⟨q, hq, rfl⟩) hlo hhi

/-! ## The bound of a child -/

/-- b is the bound of a child at compare value c among the pairs l under the
high bound hi: the next compare value, or hi after the last. -/
def IsNext (l : List (Nat × NodeId)) (hi : Option Nat) (c : Nat) (b : Option Nat) : Prop :=
  (b = hi ∧ ∀ r ∈ l, r.1 ≤ c) ∨
  (∃ r ∈ l, b = some r.1 ∧ c < r.1 ∧ ∀ r' ∈ l, c < r'.1 → r.1 ≤ r'.1)

theorem childBounds_isNext (l : List (Nat × NodeId)) (hi : Option Nat)
    (hs : l.Pairwise (fun a b => a.1 < b.1)) (q : Nat × NodeId) (b : Option Nat)
    (h : (q, b) ∈ childBounds l hi) : q ∈ l ∧ IsNext l hi q.1 b := by
  refine ⟨childBounds_fst l hi q b h, ?_⟩
  induction l with
  | nil => simp [childBounds] at h
  | cons a rest ih =>
    cases rest with
    | nil =>
      have heq : q = a ∧ b = hi := by simpa [childBounds] using h
      obtain ⟨rfl, rfl⟩ := heq
      left
      refine ⟨rfl, ?_⟩
      intro r hr
      rw [List.mem_singleton.mp hr]
      exact Nat.le_refl _
    | cons d ds =>
      rw [childBounds_cons_cons] at h
      have hsa := (List.pairwise_cons.mp hs).1
      have hsd := (List.pairwise_cons.mp hs).2
      rcases List.mem_cons.mp h with he | h
      · have heq : q = a ∧ b = some d.1 := Prod.mk.inj he
        obtain ⟨rfl, rfl⟩ := heq
        right
        have had := hsa d List.mem_cons_self
        refine ⟨d, List.mem_cons_of_mem _ List.mem_cons_self, rfl, had, ?_⟩
        intro r' hr' hlt
        rcases List.mem_cons.mp hr' with rfl | hr'
        · omega
        · rcases List.mem_cons.mp hr' with rfl | hr'
          · exact Nat.le_refl _
          · exact Nat.le_of_lt ((List.pairwise_cons.mp hsd).1 r' hr')
      · have hq' : q ∈ d :: ds := childBounds_fst _ _ _ _ h
        have haq := hsa q hq'
        rcases ih hsd h with ⟨hb, hall⟩ | ⟨r, hr, hb, hlt, hmin⟩
        · left
          refine ⟨hb, ?_⟩
          intro r hr
          rcases List.mem_cons.mp hr with rfl | hr
          · omega
          · exact hall r hr
        · right
          refine ⟨r, List.mem_cons_of_mem _ hr, hb, hlt, ?_⟩
          intro r' hr' hlt'
          rcases List.mem_cons.mp hr' with rfl | hr'
          · omega
          · exact hmin r' hr' hlt'

theorem isNext_unique (l : List (Nat × NodeId)) (hi : Option Nat) (c : Nat) (b b' : Option Nat)
    (h1 : IsNext l hi c b) (h2 : IsNext l hi c b') : b = b' := by
  rcases h1 with ⟨hb, hall⟩ | ⟨r, hr, hb, hlt, hmin⟩ <;>
    rcases h2 with ⟨hb', hall'⟩ | ⟨r', hr', hb', hlt', hmin'⟩
  · rw [hb, hb']
  · have := hall r' hr'; omega
  · have := hall' r hr; omega
  · have h3 := hmin r' hr' hlt'
    have h4 := hmin' r hr hlt
    rw [hb, hb']
    congr 1
    omega

theorem childBounds_of_isNext (l : List (Nat × NodeId)) (hi : Option Nat)
    (hs : l.Pairwise (fun a b => a.1 < b.1)) (q : Nat × NodeId) (b : Option Nat)
    (hq : q ∈ l) (h : IsNext l hi q.1 b) : (q, b) ∈ childBounds l hi := by
  obtain ⟨b', hb'⟩ := childBounds_exists l hi q hq
  have := (childBounds_isNext l hi hs q b' hb').2
  rw [isNext_unique l hi q.1 b b' h this]
  exact hb'

/-- The bound of an old child, from the old node in its range, is at most its
bound after, when every later compare value after is at least an old later
one, and the high bound after is at least the old one. -/
theorem isNext_hiLE (l0 l : List (Nat × NodeId)) (hi0 hi : Option Nat) (c : Nat) (b0 b : Option Nat)
    (h0 : IsNext l0 hi0 c b0) (h : IsNext l hi c b)
    (hold : ∀ r ∈ l0, UpperBound hi0 r.1) (hhi : HiLE hi0 hi)
    (hlater : ∀ r ∈ l, c < r.1 → ∃ r0 ∈ l0, c < r0.1 ∧ r0.1 ≤ r.1) : HiLE b0 b := by
  rcases h with ⟨hb, _⟩ | ⟨r, hr, hb, hlt, _⟩
  · rw [hb]
    rcases h0 with ⟨hb0, _⟩ | ⟨r0, hr0, hb0, _, _⟩
    · rw [hb0]; exact hhi
    · rw [hb0]
      exact hiLE_some_of_upper hi r0.1 (upperBound_of_hiLE hi0 hi r0.1 hhi (hold r0 hr0))
  · rw [hb]
    obtain ⟨r1, hr1, hlt1, hle1⟩ := hlater r hr hlt
    rcases h0 with ⟨_, hall⟩ | ⟨r0, hr0, hb0, _, hmin⟩
    · have := hall r1 hr1; omega
    · rw [hb0]
      exact ⟨r0.1, rfl, Nat.le_trans (hmin r1 hr1 hlt1) hle1⟩

/-! ## Ranges after a change -/

/-- `RangeOrder` from a predicate on the nodes reached with a range: the root
meets it, every child step keeps it, and it gives each node's range. -/
theorem rangeOrder_of_good (N : NodeId → Option KNode) (t : Time) (r : NodeId)
    (G : NodeId → Nat → Option Nat → Prop)
    (hroot : G r 0 none)
    (hinner : ∀ x lo hi n c y b, ReachR N t r x lo hi → G x lo hi → N x = some n →
      n.leaf = false → ((c, y), b) ∈ childBounds (n.liveAt t) hi →
      G y (if c == 0 then lo else c) b)
    (hseg : ∀ x lo hi n c y, ReachR N t r x lo hi → G x lo hi → N x = some n →
      n.leaf = true → (c, y) ∈ n.liveAt t → G y 0 none)
    (hrange : ∀ x lo hi n, ReachR N t r x lo hi → G x lo hi → N x = some n →
      NodeRange n t lo hi) :
    RangeOrder N t r := by
  have hG : ∀ x lo hi, ReachR N t r x lo hi → G x lo hi := by
    intro x lo hi hx
    induction hx with
    | root => exact hroot
    | inner x n lo hi c y b hx hn hl hb ih => exact hinner x lo hi n c y b hx ih hn hl hb
    | seg x n lo hi c y hx hn hl hc ih => exact hseg x lo hi n c y hx ih hn hl hc
  intro x lo hi n hx hn
  exact hrange x lo hi n hx (hG x lo hi hx) hn

theorem reachR_tReach (N : NodeId → Option KNode) (t : Time) (r x : NodeId) (lo : Nat)
    (hi : Option Nat) (h : ReachR N t r x lo hi) : TReach N t r x := by
  induction h with
  | root => exact TReach.root
  | inner x n lo hi c y b _ hn _ hb ih =>
    exact TReach.link ih ⟨n, hn, childBounds_fst _ _ _ _ hb⟩
  | seg x n lo hi c y _ hn _ hc ih => exact TReach.link ih ⟨n, hn, hc⟩

/-- An inner node x reached before with the range lo0 hi0, after with the
range lo hi at least as wide, its live klongs after l: a child (c, y) of x after
that x had before is reached before with a range at least as wide as its range
after, when every later compare value after is at least an old later one. -/
theorem old_child_step (N : NodeId → Option KNode) (t : Time) (r : NodeId)
    (hR : RangeOrder N t r) (x : NodeId) (n0 : KNode) (lo0 lo : Nat) (hi0 hi : Option Nat)
    (hx : ReachR N t r x lo0 hi0) (hn0 : N x = some n0) (hl0 : n0.leaf = false)
    (hlo : lo ≤ lo0) (hhi : HiLE hi0 hi) (l : List (Nat × NodeId))
    (hls : l.Pairwise (fun a b => a.1 < b.1))
    (c : Nat) (y y' : NodeId) (b : Option Nat) (hcy0 : (c, y) ∈ n0.liveAt t)
    (hb : ((c, y'), b) ∈ childBounds l hi)
    (hlater : ∀ r ∈ l, c < r.1 → ∃ r0 ∈ n0.liveAt t, c < r0.1 ∧ r0.1 ≤ r.1) :
    ∃ lo1 hi1, ReachR N t r y lo1 hi1 ∧ (if c == 0 then lo else c) ≤ lo1 ∧ HiLE hi1 b := by
  obtain ⟨b0, hb0⟩ := childBounds_exists (n0.liveAt t) hi0 (c, y) hcy0
  refine ⟨_, b0, ReachR.inner x n0 lo0 hi0 c y b0 hx hn0 hl0 hb0, ?_, ?_⟩
  · cases hc : (c == 0) with
    | true => simp only [↓reduceIte]; exact hlo
    | false => simp only [Bool.false_eq_true, ↓reduceIte]; exact Nat.le_refl _
  · have h0 := (childBounds_isNext _ hi0 (KNode.liveAt_order n0 t) _ _ hb0).2
    have h1 := (childBounds_isNext _ hi hls _ _ hb).2
    exact isNext_hiLE _ l hi0 hi c b0 b h0 h1 (fun q hq => (hR x lo0 hi0 n0 hx hn0 q hq).2) hhi hlater

/-! ## A time split -/

/-- The walk's ranges after a time split of x below its inner parent q, from a
tree N1 in which x holds its klongs to put (the node of the room case): the new
node y holds x's live klongs and q's klong k1 names y instead of x; x is reached
no more (N2 may hold anything at x). -/
theorem rangeOrder_timeStep (N1 N2 : NodeId → Option KNode) (t : Time) (r : NodeId)
    (hR : RangeOrder N1 t r) (hT : TreeOK N1 t r)
    (q x y : NodeId) (qn xn yn qn2 : KNode) (k1 : Nat)
    (hq : TReach N1 t r q) (hqn : N1 q = some qn) (hql : qn.leaf = false)
    (hk1 : (k1, x) ∈ qn.liveAt t) (hxn : N1 x = some xn)
    (hy1 : N1 y = none) (hyfree : ∀ u c, TReach N1 t r u → ¬ TLink N1 t u c y)
    (hN2q : N2 q = some qn2) (hq2l : qn2.leaf = false)
    (hq2 : ∀ c z, (c, z) ∈ qn2.liveAt t → (c = k1 ∧ z = y) ∨ (c ≠ k1 ∧ (c, z) ∈ qn.liveAt t))
    (hN2y : N2 y = some yn) (hyl : yn.leaf = xn.leaf) (hylive : yn.liveAt t = xn.liveAt t)
    (hN2 : ∀ z, z ≠ q → z ≠ y → z ≠ x → N2 z = N1 z) :
    RangeOrder N2 t r := by
  have hxR : TReach N1 t r x := TReach.link hq ⟨qn, hqn, hk1⟩
  have hyq : y ≠ q := by intro h; rw [h, hqn] at hy1; cases hy1
  have hyx : y ≠ x := by intro h; rw [h, hxn] at hy1; cases hy1
  have hqx : q ≠ x := by
    intro h
    exact hT.no_self_link x k1 hxR ⟨qn, by rw [← h]; exact hqn, hk1⟩
  have hrx : r ≠ x := by
    intro h; exact hT.rootFree q k1 hq ⟨qn, hqn, h ▸ hk1⟩
  have hry : r ≠ y := by
    intro h; obtain ⟨m, hm⟩ := hT.rootKey; rw [h, hy1] at hm; cases hm
  -- the only link to x is q's k1
  have honly : ∀ u c, TReach N1 t r u → TLink N1 t u c x → u = q ∧ c = k1 := fun u c hu hl =>
    hT.oneLink u c q k1 x hu hq hl ⟨qn, hqn, hk1⟩
  let φ : NodeId → NodeId := fun z => if z = y then x else z
  have hφy : φ y = x := by simp [φ]
  have hφ : ∀ z, z ≠ y → φ z = z := fun z hz => by simp [φ, hz]
  -- the node of z after, from the node of φ z before
  have hnode : ∀ z m, z ≠ q → z ≠ x → N2 z = some m →
      ∃ m0, N1 (φ z) = some m0 ∧ m.leaf = m0.leaf ∧ m.liveAt t = m0.liveAt t := by
    intro z m hzq hzx hm
    by_cases hzy : z = y
    · subst hzy; rw [hN2y] at hm; cases hm; rw [hφy]; exact ⟨xn, hxn, hyl, hylive⟩
    · rw [hN2 z hzq hzy hzx] at hm; rw [hφ z hzy]; exact ⟨m, hm, rfl, rfl⟩
  let G : NodeId → Nat → Option Nat → Prop := fun z lo hi =>
    z ≠ x ∧ ∃ lo0 hi0, ReachR N1 t r (φ z) lo0 hi0 ∧ lo ≤ lo0 ∧ HiLE hi0 hi
  -- a child after of a node reached before: not x but from q's k1, not y but from q's k1
  have hchild : ∀ u c z, TReach N1 t r u → TLink N1 t u c z → u ≠ q → z ≠ x ∧ z ≠ y := by
    intro u c z hu hl huq
    refine ⟨fun h => huq (honly u c hu (h ▸ hl)).1, fun h => hyfree u c hu (h ▸ hl)⟩
  apply rangeOrder_of_good N2 t r G
  · refine ⟨hrx, 0, none, ?_, Nat.le_refl _, HiLE.refl _⟩
    rw [hφ r hry]; exact ReachR.root
  · intro z lo hi m c z' b _ hG hm hml hb
    obtain ⟨hzx, lo0, hi0, hz0, hlo, hhi⟩ := hG
    have hcz := childBounds_fst _ _ _ _ hb
    have hms := KNode.liveAt_order m t
    by_cases hzq : z = q
    · subst hzq
      rw [hN2q] at hm; cases hm
      rw [hφ z hyq.symm] at hz0
      have hlater : ∀ r' ∈ qn2.liveAt t, c < r'.1 → ∃ r0 ∈ qn.liveAt t, c < r0.1 ∧ r0.1 ≤ r'.1 := by
        intro r' hr' hlt
        rcases hq2 r'.1 r'.2 hr' with ⟨h1, _⟩ | ⟨_, h2⟩
        · exact ⟨(k1, x), hk1, by rw [← h1]; exact hlt, by show k1 ≤ r'.1; omega⟩
        · exact ⟨r', h2, hlt, Nat.le_refl _⟩
      rcases hq2 c z' hcz with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · subst h1 h2
        obtain ⟨lo1, hi1, h3, h4, h5⟩ := old_child_step N1 t r hR z qn lo0 lo hi0 hi hz0 hqn hql hlo hhi
          _ hms c x z' b hk1 hb hlater
        exact ⟨hyx, lo1, hi1, by rw [hφy]; exact h3, h4, h5⟩
      · have hz'x : z' ≠ x := fun h => h1 (honly z c hq ⟨qn, hqn, h ▸ h2⟩).2
        have hz'y : z' ≠ y := fun h => hyfree z c hq ⟨qn, hqn, h ▸ h2⟩
        obtain ⟨lo1, hi1, h3, h4, h5⟩ := old_child_step N1 t r hR z qn lo0 lo hi0 hi hz0 hqn hql hlo hhi
          _ hms c z' z' b h2 hb hlater
        exact ⟨hz'x, lo1, hi1, by rw [hφ z' hz'y]; exact h3, h4, h5⟩
    · obtain ⟨m0, hm0, hlf, hlv⟩ := hnode z m hzq hzx hm
      have hu := reachR_tReach N1 t r (φ z) lo0 hi0 hz0
      have hcz0 : (c, z') ∈ m0.liveAt t := by rw [← hlv]; exact hcz
      have hφq : φ z ≠ q := by
        by_cases hzy : z = y
        · rw [hzy, hφy]; exact hqx.symm
        · rw [hφ z hzy]; exact hzq
      obtain ⟨hz'x, hz'y⟩ := hchild (φ z) c z' hu ⟨m0, hm0, hcz0⟩ hφq
      obtain ⟨lo1, hi1, h3, h4, h5⟩ := old_child_step N1 t r hR (φ z) m0 lo0 lo hi0 hi hz0 hm0
        (by rw [← hlf]; exact hml) hlo hhi _ hms c z' z' b hcz0 hb
        (fun r' hr' hlt => ⟨r', by rw [← hlv]; exact hr', hlt, Nat.le_refl _⟩)
      exact ⟨hz'x, lo1, hi1, by rw [hφ z' hz'y]; exact h3, h4, h5⟩
  · intro z lo hi m c z' _ hG hm hml hcz
    obtain ⟨hzx, lo0, hi0, hz0, _, _⟩ := hG
    have hzq : z ≠ q := by intro h; rw [h, hN2q] at hm; cases hm; rw [hq2l] at hml; cases hml
    obtain ⟨m0, hm0, hlf, hlv⟩ := hnode z m hzq hzx hm
    have hu := reachR_tReach N1 t r (φ z) lo0 hi0 hz0
    have hcz0 : (c, z') ∈ m0.liveAt t := by rw [← hlv]; exact hcz
    have hφq : φ z ≠ q := by
      intro h; rw [h, hqn] at hm0; cases hm0; rw [hlf, hql] at hml; cases hml
    obtain ⟨hz'x, hz'y⟩ := hchild (φ z) c z' hu ⟨m0, hm0, hcz0⟩ hφq
    refine ⟨hz'x, 0, none, ?_, Nat.le_refl _, HiLE.refl _⟩
    rw [hφ z' hz'y]
    exact ReachR.seg (φ z) m0 lo0 hi0 c z' hz0 hm0 (by rw [← hlf]; exact hml) hcz0
  · intro z lo hi m _ hG hm
    obtain ⟨hzx, lo0, hi0, hz0, hlo, hhi⟩ := hG
    by_cases hzq : z = q
    · subst hzq
      rw [hN2q] at hm; cases hm
      rw [hφ z hyq.symm] at hz0
      refine nodeRange_sub qn qn2 t lo0 lo hi0 hi (hR z lo0 hi0 qn hz0 hqn) (by rw [hq2l, hql]) ?_ hlo hhi
      intro q' hq'
      rcases hq2 q'.1 q'.2 hq' with ⟨h1, _⟩ | ⟨_, h2⟩
      · exact ⟨(k1, x), hk1, h1.symm⟩
      · exact ⟨q', h2, rfl⟩
    · obtain ⟨m0, hm0, hlf, hlv⟩ := hnode z m hzq hzx hm
      exact nodeRange_sub m0 m t lo0 lo hi0 hi (hR _ lo0 hi0 m0 hz0 hm0) hlf
        (fun q' hq' => ⟨q', by rw [← hlv]; exact hq', rfl⟩) hlo hhi

/-! ## One range per node -/

/-- In a tree, a node is reached with one range only. -/
theorem reachR_unique (N : NodeId → Option KNode) (t : Time) (r : NodeId) (hT : TreeOK N t r) :
    ∀ x lo hi, ReachR N t r x lo hi → ∀ lo' hi', ReachR N t r x lo' hi' → lo = lo' ∧ hi = hi' := by
  intro x lo hi h
  induction h with
  | root =>
    intro lo' hi' h'
    cases h' with
    | root => exact ⟨rfl, rfl⟩
    | inner p pn plo phi c _ b hp hpn _ hb =>
      exact absurd ⟨pn, hpn, childBounds_fst _ _ _ _ hb⟩
        (hT.rootFree p c (reachR_tReach N t r p plo phi hp))
    | seg p pn plo phi c _ hp hpn _ hc =>
      exact absurd ⟨pn, hpn, hc⟩ (hT.rootFree p c (reachR_tReach N t r p plo phi hp))
  | inner p pn plo phi c y b hp hpn hpl hb ih =>
    intro lo' hi' h'
    have hpR := reachR_tReach N t r p plo phi hp
    have hcy := childBounds_fst _ _ _ _ hb
    cases h' with
    | root => exact absurd ⟨pn, hpn, hcy⟩ (hT.rootFree p c hpR)
    | inner p' pn' plo' phi' c' _ b' hp' hpn' _ hb' =>
      obtain ⟨he, hc⟩ := hT.oneLink p c p' c' y hpR (reachR_tReach N t r p' plo' phi' hp')
        ⟨pn, hpn, hcy⟩ ⟨pn', hpn', childBounds_fst _ _ _ _ hb'⟩
      subst he hc
      rw [hpn] at hpn'; cases hpn'
      obtain ⟨h1, h2⟩ := ih plo' phi' hp'
      subst h1 h2
      have := isNext_unique _ _ _ _ _ (childBounds_isNext _ _ (KNode.liveAt_order pn t) _ _ hb).2
        (childBounds_isNext _ _ (KNode.liveAt_order pn t) _ _ hb').2
      exact ⟨rfl, this⟩
    | seg p' pn' plo' phi' c' _ hp' hpn' hpl' hc' =>
      obtain ⟨he, _⟩ := hT.oneLink p c p' c' y hpR (reachR_tReach N t r p' plo' phi' hp')
        ⟨pn, hpn, hcy⟩ ⟨pn', hpn', hc'⟩
      subst he
      rw [hpn] at hpn'; cases hpn'
      rw [hpl] at hpl'; cases hpl'
  | seg p pn plo phi c y hp hpn hpl hc ih =>
    intro lo' hi' h'
    have hpR := reachR_tReach N t r p plo phi hp
    cases h' with
    | root => exact absurd ⟨pn, hpn, hc⟩ (hT.rootFree p c hpR)
    | inner p' pn' plo' phi' c' _ b' hp' hpn' hpl' hb' =>
      obtain ⟨he, _⟩ := hT.oneLink p c p' c' y hpR (reachR_tReach N t r p' plo' phi' hp')
        ⟨pn, hpn, hc⟩ ⟨pn', hpn', childBounds_fst _ _ _ _ hb'⟩
      subst he
      rw [hpn] at hpn'; cases hpn'
      rw [hpl] at hpl'; cases hpl'
    | seg => exact ⟨rfl, rfl⟩

/-! ## The ranges of a descent -/

/-- A node reached with a range holding cv: the descent for cv from it visits
nodes reached with ranges holding cv. -/
theorem eqVisits_reachR (N : NodeId → Option KNode) (t : Time) (r : NodeId) (cv : Nat) :
    ∀ (f : Nat) (x z : NodeId) (c lo : Nat) (hi : Option Nat), ReachR N t r x lo hi → lo ≤ cv →
      UpperBound hi cv → (z, c) ∈ eqVisits N t cv f x →
      ∃ lo' hi', ReachR N t r z lo' hi' ∧ lo' ≤ cv ∧ UpperBound hi' cv := by
  intro f
  induction f with
  | zero => intro x z c lo hi _ _ _ h; simp [eqVisits] at h
  | succ f ih =>
    intro x z c lo hi hx hlo hhi h
    simp only [eqVisits, List.mem_cons, Prod.mk.injEq] at h
    rcases h with ⟨rfl, _⟩ | h
    · exact ⟨lo, hi, hx, hlo, hhi⟩
    · cases hn : N x with
      | none => rw [hn] at h; cases h
      | some n =>
        rw [hn] at h
        simp only at h
        split at h
        · cases h
        · rename_i hnl
          cases hf : n.searchLte t cv with
          | none => rw [hf] at h; cases h
          | some fd =>
            rw [hf] at h
            obtain ⟨hmem, hle, hmax⟩ := (n.searchLte_spec t cv).1 fd hf
            simp only [decide_eq_true_eq] at hle
            obtain ⟨b, hb⟩ := childBounds_exists (n.liveAt t) hi (fd.c, fd.y) hmem
            have hx' := ReachR.inner x n lo hi fd.c fd.y b hx hn (by simpa using hnl) hb
            refine ih fd.y z c _ b hx' ?_ ?_ h
            · cases hc : (fd.c == 0) with
              | true => simp only [↓reduceIte]; exact hlo
              | false => simp only [Bool.false_eq_true, ↓reduceIte]; omega
            · rcases (childBounds_isNext _ hi (KNode.liveAt_order n t) _ _ hb).2 with
                ⟨hb', _⟩ | ⟨r', hr', hb', hlt, _⟩
              · rw [hb']; exact hhi
              · rw [hb']
                simp only [UpperBound]
                have := hmax r' hr'
                rcases Nat.lt_or_ge cv r'.1 with hcv | hcv
                · exact hcv
                · have h2 := this (by simp; omega)
                  simp only [decide_eq_true_eq] at h2
                  simp only at hlt
                  omega

/-- The node a segment's reading reaches from a reached node is reached with
the whole range, a segment root. -/
theorem getEqR_reachR (N : NodeId → Option KNode) (t : Time) (r : NodeId) (cv : Nat)
    (hwf : ∀ x xn, N x = some xn → klongsWf xn.ks = true) :
    ∀ (f : Nat) (x y : NodeId) (lo : Nat) (hi : Option Nat), ReachR N t r x lo hi →
      getEqR N t cv f x = some y → ReachR N t r y 0 none := by
  intro f
  induction f with
  | zero => intro x y lo hi _ h; simp [getEqR] at h
  | succ f ih =>
    intro x y lo hi hx h
    simp only [getEqR] at h
    cases hn : N x with
    | none => rw [hn] at h; cases h
    | some n =>
      rw [hn] at h
      simp only at h
      split at h
      · rename_i hnl
        cases hf : n.searchEq t cv with
        | none => rw [hf] at h; cases h
        | some fd =>
          rw [hf] at h
          simp only [Option.map_some, Option.some.injEq] at h
          subst h
          exact ReachR.seg x n lo hi cv fd.y hx hn hnl (KNode.searchEq_mem n t cv fd (hwf x n hn) hf)
      · rename_i hnl
        cases hf : n.searchLte t cv with
        | none => rw [hf] at h; cases h
        | some fd =>
          rw [hf] at h
          obtain ⟨b, hb⟩ := childBounds_exists (n.liveAt t) hi (fd.c, fd.y)
            (KNode.searchLte_mem n t cv fd hf)
          exact ih fd.y y _ b (ReachR.inner x n lo hi fd.c fd.y b hx hn (by simpa using hnl) hb) h

/-- A segment root on a key's path is reached with the whole range. -/
theorem segRootR_reachR (N : NodeId → Option KNode) (t : Time) (fuel : Nat) (r0 : NodeId)
    (hwf : ∀ x xn, N x = some xn → klongsWf xn.ks = true) :
    ∀ (pre : List Nat) (x rk : NodeId), ReachR N t r0 x 0 none → segRootR N t fuel pre x = some rk →
      ReachR N t r0 rk 0 none := by
  intro pre
  induction pre with
  | nil => intro x rk hx h; simp only [segRootR, Option.some.injEq] at h; subst h; exact hx
  | cons c rest ih =>
    intro x rk hx h
    simp only [segRootR] at h
    cases hg : getEqR N t c fuel x with
    | none => rw [hg] at h; cases h
    | some y =>
      rw [hg] at h
      simp only at h
      split at h
      · exact ih y rk (getEqR_reachR N t r0 c hwf fuel x y 0 none hx hg) h
      · cases h

/-- The leaf of a key's last segment cv is reached, in a tree, with a range
holding cv only. -/
theorem leaf_range (N : NodeId → Option KNode) (t : Time) (r : NodeId) (hT : TreeOK N t r)
    (hwf : ∀ x xn, N x = some xn → klongsWf xn.ks = true) (fuel : Nat) (pre : List Nat) (cv : Nat)
    (rk L : NodeId) (hrk : segRootR N t fuel pre r = some rk)
    (hL : (L, cv) ∈ eqVisits N t cv fuel rk) :
    ∀ lo hi, ReachR N t r L lo hi → lo ≤ cv ∧ UpperBound hi cv := by
  have hrkR := segRootR_reachR N t fuel r hwf pre r rk ReachR.root hrk
  obtain ⟨lo', hi', hL', hlo', hhi'⟩ := eqVisits_reachR N t r cv fuel rk L cv 0 none hrkR
    (Nat.zero_le _) trivial hL
  intro lo hi h
  obtain ⟨h1, h2⟩ := reachR_unique N t r hT L lo hi h lo' hi' hL'
  subst h1 h2
  exact ⟨hlo', hhi'⟩

/-! ## One node changed -/

/-- The walk's ranges after one node x changes to m, its flag kept: m in each
range x had, its children x's or nodes there are none of, an inner m's later
compare values after an old child at least an old later one of x. -/
theorem rangeOrder_nodeChange (N N' : NodeId → Option KNode) (t : Time) (r x : NodeId) (n m : KNode)
    (hR : RangeOrder N t r) (hxn : N x = some n) (hN'x : N' x = some m) (hml : m.leaf = n.leaf)
    (hN' : ∀ z, z ≠ x → N' z = N z)
    (hrange : ∀ lo hi, ReachR N t r x lo hi → NodeRange m t lo hi)
    (hkids : ∀ c z, (c, z) ∈ m.liveAt t → (c, z) ∈ n.liveAt t ∨ N' z = none)
    (hlater : m.leaf = false → ∀ c z, (c, z) ∈ m.liveAt t → (c, z) ∈ n.liveAt t →
      ∀ r' ∈ m.liveAt t, c < r'.1 → ∃ r0 ∈ n.liveAt t, c < r0.1 ∧ r0.1 ≤ r'.1) :
    RangeOrder N' t r := by
  let G : NodeId → Nat → Option Nat → Prop := fun z lo hi =>
    (∃ lo0 hi0, ReachR N t r z lo0 hi0 ∧ lo ≤ lo0 ∧ HiLE hi0 hi) ∨ N' z = none
  -- the old node of z and its live klongs
  have hold : ∀ z m', N' z = some m' → z ≠ x → N z = some m' := by
    intro z m' h hz; rw [← hN' z hz]; exact h
  apply rangeOrder_of_good N' t r G
  · exact Or.inl ⟨0, none, ReachR.root, Nat.le_refl _, HiLE.refl _⟩
  · intro z lo hi m' c z' b _ hG hm hml' hb
    rcases hG with ⟨lo0, hi0, hz0, hlo, hhi⟩ | hG
    · have hcz := childBounds_fst _ _ _ _ hb
      have hms := KNode.liveAt_order m' t
      by_cases hzx : z = x
      · subst hzx
        rw [hN'x] at hm; cases hm
        rcases hkids c z' hcz with hc0 | hc0
        · exact Or.inl (old_child_step N t r hR z n lo0 lo hi0 hi hz0 hxn (by rw [← hml]; exact hml')
            hlo hhi _ hms c z' z' b hc0 hb (hlater hml' c z' hcz hc0))
        · exact Or.inr hc0
      · have hm0 := hold z m' hm hzx
        exact Or.inl (old_child_step N t r hR z m' lo0 lo hi0 hi hz0 hm0 hml' hlo hhi _ hms c z' z' b
          hcz hb (fun r' hr' hlt => ⟨r', hr', hlt, Nat.le_refl _⟩))
    · rw [hG] at hm; cases hm
  · intro z lo hi m' c z' _ hG hm hml' hcz
    rcases hG with ⟨lo0, hi0, hz0, _, _⟩ | hG
    · by_cases hzx : z = x
      · subst hzx
        rw [hN'x] at hm; cases hm
        rcases hkids c z' hcz with hc0 | hc0
        · exact Or.inl ⟨0, none, ReachR.seg z n lo0 hi0 c z' hz0 hxn (by rw [← hml]; exact hml') hc0,
            Nat.le_refl _, HiLE.refl _⟩
        · exact Or.inr hc0
      · have hm0 := hold z m' hm hzx
        exact Or.inl ⟨0, none, ReachR.seg z m' lo0 hi0 c z' hz0 hm0 hml' hcz, Nat.le_refl _,
          HiLE.refl _⟩
    · rw [hG] at hm; cases hm
  · intro z lo hi m' _ hG hm
    rcases hG with ⟨lo0, hi0, hz0, hlo, hhi⟩ | hG
    · by_cases hzx : z = x
      · subst hzx
        rw [hN'x] at hm; cases hm
        exact nodeRange_wider m t lo0 lo hi0 hi (hrange lo0 hi0 hz0) hlo hhi
      · exact nodeRange_wider m' t lo0 lo hi0 hi (hR z lo0 hi0 m' hz0 (hold z m' hm hzx)) hlo hhi
    · rw [hG] at hm; cases hm

/-- The walk's ranges kept when the nodes change only where nothing reached
before is. -/
theorem rangeOrder_agree (N N' : NodeId → Option KNode) (t : Time) (r : NodeId)
    (hR : RangeOrder N t r) (hag : ∀ z, TReach N t r z → N' z = N z) : RangeOrder N' t r := by
  have hsub : ∀ z lo hi, ReachR N' t r z lo hi → ReachR N t r z lo hi := by
    intro z lo hi h
    induction h with
    | root => exact ReachR.root
    | inner x n lo hi c y b _ hn hl hb ih =>
      rw [hag x (reachR_tReach N t r x lo hi ih)] at hn
      exact ReachR.inner x n lo hi c y b ih hn hl hb
    | seg x n lo hi c y _ hn hl hc ih =>
      rw [hag x (reachR_tReach N t r x lo hi ih)] at hn
      exact ReachR.seg x n lo hi c y ih hn hl hc
  intro z lo hi m h hm
  have h0 := hsub z lo hi h
  rw [hag z (reachR_tReach N t r z lo hi h0)] at hm
  exact hR z lo hi m h0 hm

end SIS.Tree
