import SIS.Tree.RangeOps
import SIS.Tree.RangeCollapse
import SIS.Tree.GetDelCascade
import SIS.Tree.PutInvDelFull
import SIS.Tree.GetInnerSplit
import SIS.Tree.WriterTreeLeb

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! LE-b keeps the walk's ranges (bergdb 024-12, TP10; `RangeOrder`): the empty
key of an inner node x takes the child of x's next live klong (jcv, jy), and
jcv is deleted. jcv is the least live compare value of x above 0 (`lebMin_fold`),
so jy's range after, from x's own low bound to the compare value after jcv, holds
its range before, from jcv (`rangeOrder_leb`). -/

/-! ## The next klong is the least -/

/-- LE-b's fold so far: nothing chosen, every key klong in the bitmap; a choice
of compare value cv, at most the compare value of every key klong the bitmap
keeps. -/
def LebMin (ks : List Klong) (del : List Nat) (best : Option (Nat × Nat × NodeId)) : Prop :=
  (best = none → ∀ j c y, ks[j]? = some (.key c y) → j ∈ del) ∧
  (∀ i cv y, best = some (i, cv, y) → ∀ j c y', ks[j]? = some (.key c y') → j ∉ del → cv ≤ c)

theorem lebMin_step (ks : List Klong) (del : List Nat) (best : Option (Nat × Nat × NodeId))
    (k : Klong) (hb : LebMin ks del best) :
    LebMin (ks ++ [k]) del (lebStep del best (k, ks.length)) := by
  obtain ⟨hnone, hsome⟩ := hb
  have hsplit : ∀ j c' y', (ks ++ [k])[j]? = some (.key c' y') →
      ks[j]? = some (.key c' y') ∨ (j = ks.length ∧ k = .key c' y') := by
    intro j c' y' hj
    rcases Nat.lt_trichotomy j ks.length with h1 | h1 | h1
    · rw [getElem?_append_single_lt _ _ _ h1] at hj; exact Or.inl hj
    · subst h1; rw [getElem?_append_single_eq] at hj
      simp only [Option.some.injEq] at hj
      exact Or.inr ⟨rfl, hj⟩
    · rw [getElem?_append_single_gt _ _ _ h1] at hj; cases hj
  unfold lebStep
  cases k with
  | time tt =>
    refine ⟨fun h j c y hj => ?_, fun i cv y h j c y' hj hd => ?_⟩
    · rcases hsplit j c y hj with h1 | ⟨_, h1⟩
      · exact hnone h j c y h1
      · cases h1
    · rcases hsplit j c y' hj with h1 | ⟨_, h1⟩
      · exact hsome i cv y h j c y' h1 hd
      · cases h1
  | del b =>
    refine ⟨fun h j c y hj => ?_, fun i cv y h j c y' hj hd => ?_⟩
    · rcases hsplit j c y hj with h1 | ⟨_, h1⟩
      · exact hnone h j c y h1
      · cases h1
    · rcases hsplit j c y' hj with h1 | ⟨_, h1⟩
      · exact hsome i cv y h j c y' h1 hd
      · cases h1
  | key c0 y0 =>
    simp only
    by_cases hd : del.contains ks.length = true
    · simp only [hd, ↓reduceIte]
      have hd' : ks.length ∈ del := by simpa using hd
      refine ⟨fun h j c y hj => ?_, fun i cv y h j c y' hj hdj => ?_⟩
      · rcases hsplit j c y hj with h1 | ⟨h1, _⟩
        · exact hnone h j c y h1
        · rw [h1]; exact hd'
      · rcases hsplit j c y' hj with h1 | ⟨h1, _⟩
        · exact hsome i cv y h j c y' h1 hdj
        · exact absurd (h1 ▸ hd') hdj
    · simp only [hd, Bool.false_eq_true, ↓reduceIte]
      cases best with
      | none =>
        simp only
        refine ⟨fun h => (by cases h), fun i cv y h j c y' hj hdj => ?_⟩
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨_, rfl, _⟩ := h
        rcases hsplit j c y' hj with h1 | ⟨_, h1⟩
        · exact absurd (hnone rfl j c y' h1) hdj
        · simp only [Klong.key.injEq] at h1; omega
      | some bb =>
        obtain ⟨i0, jcv, jy⟩ := bb
        simp only
        split
        · rename_i hle
          refine ⟨fun h => (by cases h), fun i cv y h j c y' hj hdj => ?_⟩
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨_, rfl, _⟩ := h
          rcases hsplit j c y' hj with h1 | ⟨_, h1⟩
          · have := hsome i0 jcv jy rfl j c y' h1 hdj; omega
          · simp only [Klong.key.injEq] at h1; omega
        · rename_i hle
          refine ⟨fun h => (by cases h), fun i cv y h j c y' hj hdj => ?_⟩
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          rcases hsplit j c y' hj with h1 | ⟨_, h1⟩
          · exact hsome i0 jcv jy rfl j c y' h1 hdj
          · simp only [Klong.key.injEq] at h1; omega

theorem lebMin_fold (del : List Nat) (ks : List Klong) :
    LebMin ks del (ks.zipIdx.foldl (lebStep del) none) := by
  have key : ∀ rs : List Klong, LebMin rs.reverse del (rs.reverse.zipIdx.foldl (lebStep del) none) := by
    intro rs
    induction rs with
    | nil =>
      refine ⟨fun _ j c y hj => ?_, fun _ _ _ h => (by cases h)⟩
      simp at hj
    | cons k rs ih =>
      rw [List.reverse_cons, List.zipIdx_append, List.foldl_append]
      simp only [List.zipIdx_cons, List.zipIdx_nil, Nat.zero_add, List.foldl_cons, List.foldl_nil]
      exact lebMin_step rs.reverse del _ k ih
  have := key ks.reverse
  rwa [List.reverse_reverse] at this

/-- LE-b's next klong has the least live compare value above 0. -/
theorem leb_min_live (n : KNode) (j0 jcv : Nat) (jy : NodeId)
    (hJ : n.ks.zipIdx.foldl (lebStep (bitsUnion n.lastBitmap (n.bitsOf 0))) none = some (j0, jcv, jy)) :
    ∀ c z, (c, z) ∈ n.live → c ≠ 0 → jcv ≤ c := by
  intro c z hz hc
  have hl := lookup_of_mem_nodup _ (KNode.live_keys_nodup n) c z hz
  rw [KNode.live_lookup] at hl
  unfold keyLookup at hl
  rcases keyLookupFold_source_live _ _ _ _ _ hl with hh | ⟨j, hj, hd⟩
  · cases hh
  · have hjk : n.ks[j]? = some (.key c z) := List.mem_zipIdx_iff_getElem?.mp hj
    have hd0 : j ∉ bitsUnion n.lastBitmap (n.bitsOf 0) := by
      intro hm
      rcases (mem_bitsUnion_iff _ _ _).mp hm with h1 | h1
      · exact hd h1
      · obtain ⟨y', hy'⟩ := (n.mem_bitsOf_iff 0 j).mp h1
        rw [List.mem_zipIdx_iff_getElem?.mp hy'] at hjk
        simp only [Option.some.injEq, Klong.key.injEq] at hjk
        exact hc hjk.1.symm
    exact (lebMin_fold _ n.ks).2 j0 jcv jy hJ j c z hjk hd0

/-! ## The ranges -/

/-- The walk's ranges after LE-b at the inner node x: its live klongs after are
the empty key to jy, x's next child at jcv, the least live compare value above
0, and x's others but jcv. -/
theorem rangeOrder_leb (N N' : NodeId → Option KNode) (t : Time) (r x : NodeId) (n n2 : KNode)
    (jcv : Nat) (jy : NodeId) (hR : RangeOrder N t r) (hxn : N x = some n) (hxl : n.leaf = false)
    (hN'x : N' x = some n2) (hn2l : n2.leaf = false) (hN' : ∀ z, z ≠ x → N' z = N z)
    (hj : (jcv, jy) ∈ n.liveAt t) (hj0 : jcv ≠ 0)
    (hmin : ∀ c z, (c, z) ∈ n.liveAt t → c ≠ 0 → jcv ≤ c)
    (hn2 : ∀ cc z, (cc, z) ∈ n2.liveAt t → (cc = 0 ∧ z = jy) ∨ ((cc, z) ∈ n.liveAt t ∧ cc ≠ jcv)) :
    RangeOrder N' t r := by
  let G : NodeId → Nat → Option Nat → Prop := fun z lo hi =>
    ∃ lo0 hi0, ReachR N t r z lo0 hi0 ∧ lo ≤ lo0 ∧ HiLE hi0 hi
  have hold : ∀ z m, N' z = some m → z ≠ x → N z = some m := by
    intro z m h hz; rw [← hN' z hz]; exact h
  -- the compare values after jcv of x after are x's before
  have hlater : ∀ c, ∀ r' ∈ n2.liveAt t, c < r'.1 → ∃ r0 ∈ n.liveAt t, c < r0.1 ∧ r0.1 ≤ r'.1 := by
    intro c r' hr' hlt
    rcases hn2 r'.1 r'.2 hr' with ⟨h1, _⟩ | ⟨h1, _⟩
    · omega
    · exact ⟨r', h1, hlt, Nat.le_refl _⟩
  apply rangeOrder_of_good N' t r G
  · exact ⟨0, none, ReachR.root, Nat.le_refl _, HiLE.refl _⟩
  · intro z lo hi m c z' b _ hG hm hml hb
    obtain ⟨lo0, hi0, hz0, hlo, hhi⟩ := hG
    have hcz := childBounds_fst _ _ _ _ hb
    have hms := KNode.liveAt_order m t
    by_cases hzx : z = x
    · rw [hzx, hN'x] at hm; cases hm
      rw [hzx] at hz0
      have hxr := hR x lo0 hi0 n hz0 hxn
      rcases hn2 c z' hcz with ⟨h1, h2⟩ | ⟨h1, _⟩
      · rw [h1, h2] at hb ⊢
        obtain ⟨b0, hb0⟩ := childBounds_exists (n.liveAt t) hi0 (jcv, jy) hj
        refine ⟨_, b0, ReachR.inner x n lo0 hi0 jcv jy b0 hz0 hxn hxl hb0, ?_, ?_⟩
        · rw [ite_zero_eq jcv lo0 hj0]
          simp only [beq_self_eq_true, ↓reduceIte]
          have := (hxr (jcv, jy) hj).1
          simp only [hxl, Bool.false_eq_true, ↓reduceIte] at this
          omega
        · refine isNext_hiLE2 _ _ hi0 hi jcv 0 b0 b
            (childBounds_isNext _ hi0 (KNode.liveAt_order n t) _ _ hb0).2
            (childBounds_isNext _ _ hms _ _ hb).2 (Or.inl hhi) (fun r' hr' => (hxr r' hr').2) ?_
          intro r' hr' hlt
          rcases hn2 r'.1 r'.2 hr' with ⟨h3, _⟩ | ⟨h3, h4⟩
          · omega
          · have := hmin r'.1 r'.2 h3 (by omega)
            exact ⟨r', h3, by omega, Nat.le_refl _⟩
      · exact old_child_step N t r hR x n lo0 lo hi0 hi hz0 hxn hxl hlo hhi _ hms c z' z' b h1 hb
          (hlater c)
    · exact old_child_step N t r hR z m lo0 lo hi0 hi hz0 (hold z m hm hzx) hml hlo hhi _ hms c z' z'
        b hcz hb (fun r' hr' hlt => ⟨r', hr', hlt, Nat.le_refl _⟩)
  · intro z lo hi m c z' _ hG hm hml hcz
    obtain ⟨lo0, hi0, hz0, _, _⟩ := hG
    have hzx : z ≠ x := by intro h; rw [h, hN'x] at hm; cases hm; rw [hn2l] at hml; cases hml
    exact ⟨0, none, ReachR.seg z m lo0 hi0 c z' hz0 (hold z m hm hzx) hml hcz, Nat.le_refl _,
      HiLE.refl _⟩
  · intro z lo hi m _ hG hm
    obtain ⟨lo0, hi0, hz0, hlo, hhi⟩ := hG
    by_cases hzx : z = x
    · rw [hzx, hN'x] at hm; cases hm
      rw [hzx] at hz0
      have hxr := hR x lo0 hi0 n hz0 hxn
      intro q hq
      simp only [hn2l, Bool.false_eq_true, ↓reduceIte]
      rcases hn2 q.1 q.2 hq with ⟨h1, _⟩ | ⟨h1, _⟩
      · refine ⟨Or.inl h1, ?_⟩
        have hju := (hxr (jcv, jy) hj).2
        rw [h1]
        refine upperBound_of_hiLE hi0 hi 0 hhi ?_
        cases hi0 with
        | none => trivial
        | some h0 => simp only [UpperBound] at hju ⊢; omega
      · obtain ⟨h3, h4⟩ := hxr q h1
        simp only [hxl, Bool.false_eq_true, ↓reduceIte] at h3
        exact ⟨by omega, upperBound_of_hiLE hi0 hi q.1 hhi h4⟩
    · exact nodeRange_wider m t lo0 lo hi0 hi (hR z lo0 hi0 m hz0 (hold z m hm hzx)) hlo hhi

/-! ## LE-b at the writer -/

theorem lebNode_leaf (n : KNode) (tt : Time) (htd lip : Bool) (e jcv : Nat) (jy : NodeId) :
    (lebNode n tt htd lip e jcv jy).leaf = n.leaf := by
  unfold lebNode
  cases htd <;> cases lip <;> simp [bk_repoint_leaf, KNode.add_leaf, KNode.setAt_leaf]

end SIS.Tree
