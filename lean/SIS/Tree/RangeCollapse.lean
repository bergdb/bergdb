import SIS.Tree.RangeSteps
import SIS.Tree.WriterTreeCollapse
import SIS.Tree.GetDelCascade
import SIS.Tree.PutInvDelFull
import SIS.Tree.GetInnerSplit
import SIS.Tree.GetSpaceSpace

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! The walk's ranges after a root collapse (bergdb 024-12, TP10;
`RangeOrder`): a root whose one live klong is the empty key to y gives way to
y, which was reached with the whole range (`rangeOrder_collapseRoot`; below a
segment leaf, `rangeOrder_segCollapse`). `onlyLiveKlong` finds the one live
klong: every live klong of the node has its compare value
(`onlyLiveKlong_live`). -/

/-! ## The one live klong -/

/-- `onlyLiveKlong`'s fold so far: nothing chosen, every key klong deleted; a
choice of compare value c, every key klong the bitmap keeps of c. -/
def OnlySame (ks : List Klong) (del : List Nat) (acc : Option (Option (Nat × Nat))) : Prop :=
  (acc = some none → ∀ j c' y', ks[j]? = some (.key c' y') → j ∈ del) ∧
  (∀ i c, acc = some (some (i, c)) → ∀ j c' y', ks[j]? = some (.key c' y') → j ∉ del → c' = c)

theorem onlySame_step (ks : List Klong) (del : List Nat) (acc : Option (Option (Nat × Nat)))
    (k : Klong) (ha : OnlySame ks del acc) :
    OnlySame (ks ++ [k]) del (onlyStep del acc (k, ks.length)) := by
  obtain ⟨hnone, hsome⟩ := ha
  -- a key klong of ks ++ [k]: one of ks, or k at ks.length
  have hsplit : ∀ j c' y', (ks ++ [k])[j]? = some (.key c' y') →
      ks[j]? = some (.key c' y') ∨ (j = ks.length ∧ k = .key c' y') := by
    intro j c' y' hj
    rcases Nat.lt_trichotomy j ks.length with h1 | h1 | h1
    · rw [getElem?_append_single_lt _ _ _ h1] at hj; exact Or.inl hj
    · subst h1; rw [getElem?_append_single_eq] at hj
      simp only [Option.some.injEq] at hj
      exact Or.inr ⟨rfl, hj⟩
    · rw [getElem?_append_single_gt _ _ _ h1] at hj; cases hj
  unfold onlyStep
  cases acc with
  | none => exact ⟨fun h => (by cases h), fun _ _ h => (by cases h)⟩
  | some cur =>
    simp only
    cases k with
    | time tt =>
      refine ⟨fun h j c' y' hj => ?_, fun i c h j c' y' hj hd => ?_⟩
      · rcases hsplit j c' y' hj with h1 | ⟨_, h1⟩
        · exact hnone h j c' y' h1
        · cases h1
      · rcases hsplit j c' y' hj with h1 | ⟨_, h1⟩
        · exact hsome i c h j c' y' h1 hd
        · cases h1
    | del b =>
      refine ⟨fun h j c' y' hj => ?_, fun i c h j c' y' hj hd => ?_⟩
      · rcases hsplit j c' y' hj with h1 | ⟨_, h1⟩
        · exact hnone h j c' y' h1
        · cases h1
      · rcases hsplit j c' y' hj with h1 | ⟨_, h1⟩
        · exact hsome i c h j c' y' h1 hd
        · cases h1
    | key c0 y0 =>
      simp only
      by_cases hd : del.contains ks.length = true
      · simp only [hd, ↓reduceIte]
        have hd' : ks.length ∈ del := by simpa using hd
        refine ⟨fun h j c' y' hj => ?_, fun i c h j c' y' hj hdj => ?_⟩
        · rcases hsplit j c' y' hj with h1 | ⟨h1, _⟩
          · exact hnone h j c' y' h1
          · rw [h1]; exact hd'
        · rcases hsplit j c' y' hj with h1 | ⟨h1, _⟩
          · exact hsome i c h j c' y' h1 hdj
          · exact absurd (h1 ▸ hd') hdj
      · simp only [hd, Bool.false_eq_true, ↓reduceIte]
        have hd' : ks.length ∉ del := by simpa using hd
        cases cur with
        | none =>
          simp only
          refine ⟨fun h => (by cases h), fun i c h j c' y' hj hdj => ?_⟩
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨_, rfl⟩ := h
          rcases hsplit j c' y' hj with h1 | ⟨_, h1⟩
          · exact absurd (hnone rfl j c' y' h1) hdj
          · simp only [Klong.key.injEq] at h1; exact h1.1.symm
        | some pc =>
          rcases pc with ⟨i0, cv⟩
          simp only
          split
          · exact ⟨fun h => (by cases h), fun _ _ h => (by cases h)⟩
          · rename_i hne
            have hcv : c0 = cv := by simpa using hne
            refine ⟨fun h => (by cases h), fun i c h j c' y' hj hdj => ?_⟩
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨_, rfl⟩ := h
            rcases hsplit j c' y' hj with h1 | ⟨_, h1⟩
            · rw [hsome i0 cv rfl j c' y' h1 hdj, hcv]
            · simp only [Klong.key.injEq] at h1; exact h1.1.symm

theorem onlySame_fold (del : List Nat) (ks : List Klong) :
    OnlySame ks del (ks.zipIdx.foldl (onlyStep del) (some none)) := by
  have key : ∀ rs : List Klong, OnlySame rs.reverse del
      (rs.reverse.zipIdx.foldl (onlyStep del) (some none)) := by
    intro rs
    induction rs with
    | nil =>
      refine ⟨fun _ j c' y' hj => ?_, fun _ _ h => by cases h⟩
      simp at hj
    | cons k rs ih =>
      rw [List.reverse_cons, List.zipIdx_append, List.foldl_append]
      simp only [List.zipIdx_cons, List.zipIdx_nil, Nat.zero_add, List.foldl_cons, List.foldl_nil]
      exact onlySame_step rs.reverse del _ k ih
  have := key ks.reverse
  rwa [List.reverse_reverse] at this

/-- `keyLookup` finds a key klong the bitmap keeps. -/
theorem keyLookupFold_source_live (xs : List (Klong × Nat)) (del : List Nat)
    (c : Nat) (v : Option NodeId) (y : NodeId)
    (he : xs.foldl (keyLookupStep del c) v = some y) :
    v = some y ∨ ∃ j, (.key c y, j) ∈ xs ∧ j ∉ del := by
  induction xs generalizing v with
  | nil => exact Or.inl he
  | cons q qs ih =>
    rcases ih _ he with hh | ⟨j, hj, hd⟩
    · rcases q with ⟨k, j⟩
      cases k with
      | time tt => exact Or.inl hh
      | del b => exact Or.inl hh
      | key a z =>
        simp only [keyLookupStep] at hh
        split at hh
        · exact Or.inl hh
        · rename_i hdel
          split at hh
          · rename_i hac
            have hac' : a = c := by simpa using hac
            have hzy : z = y := Option.some.inj hh
            subst hac' hzy
            exact Or.inr ⟨j, List.mem_cons_self, by simpa using hdel⟩
          · exact Or.inl hh
    · exact Or.inr ⟨j, List.mem_cons_of_mem _ hj, hd⟩

/-- Every live klong of a node whose `onlyLiveKlong` is the key klong i has i's
compare value. -/
theorem onlyLiveKlong_live (n : KNode) (i c : Nat) (y : NodeId) (h : n.onlyLiveKlong = some i)
    (hk : n.ks[i]? = some (.key c y)) : ∀ c' z, (c', z) ∈ n.live → c' = c := by
  intro c' z hz
  have hl := lookup_of_mem_nodup _ (KNode.live_keys_nodup n) c' z hz
  rw [KNode.live_lookup] at hl
  unfold keyLookup at hl
  rcases keyLookupFold_source_live _ _ _ _ _ hl with hh | ⟨j, hj, hd⟩
  · cases hh
  · have hjk : n.ks[j]? = some (.key c' z) := List.mem_zipIdx_iff_getElem?.mp hj
    have hf := onlySame_fold n.lastBitmap n.ks
    unfold KNode.onlyLiveKlong at h
    simp only at h
    split at h
    · rename_i i0 c0 hr
      simp only [Option.some.injEq] at h
      subst h
      have hr' : n.ks.zipIdx.foldl (onlyStep n.lastBitmap) (some none) = some (some (i0, c0)) := hr
      rw [hr'] at hf
      have h1 := hf.2 i0 c0 rfl j c' z hjk hd
      obtain ⟨⟨y0, hy0⟩, _, _⟩ := onlyOK_fold n.lastBitmap n.ks i0 c0 hr'
      rw [hk] at hy0
      simp only [Option.some.injEq, Klong.key.injEq] at hy0
      rw [h1, hy0.1]
    · cases h

/-- The live klongs of a root that collapses: the one klong of its only live
klong's compare value, to its child. -/
theorem onlyLiveKlong_liveAt (n : KNode) (t : Time) (i : Nat) (y : NodeId)
    (hnt : ∀ s, Klong.time s ∈ n.ks → s ≤ t) (h : n.onlyLiveKlong = some i)
    (hy : n.ptr? i = some y) (hc : n.cv? i = some 0) :
    (0, y) ∈ n.liveAt t ∧ ∀ c z, (c, z) ∈ n.liveAt t → c = 0 ∧ z = y := by
  obtain ⟨c, y0, hk, hl⟩ := onlyLiveKlong_last n i h
  have hy0 : y0 = y := by simp only [KNode.ptr?, hk, Option.some.injEq] at hy; exact hy
  have hc0 : c = 0 := by simp only [KNode.cv?, hk, Option.some.injEq] at hc; exact hc
  subst hy0 hc0
  have hmem : (0, y0) ∈ n.liveAt t := by
    rw [KNode.liveAt_of_times n t hnt]
    apply bk_mem_of_lookup
    rw [KNode.live_lookup]
    exact keyLookup_of_last _ _ _ i y0 hk hl
  refine ⟨hmem, ?_⟩
  intro c z hz
  rw [KNode.liveAt_of_times n t hnt] at hz hmem
  have hc := onlyLiveKlong_live n i 0 y0 h hk c z hz
  subst hc
  have h1 := lookup_of_mem_nodup _ (KNode.live_keys_nodup n) _ z hz
  have h2 := lookup_of_mem_nodup _ (KNode.live_keys_nodup n) _ y0 hmem
  rw [h1] at h2
  exact ⟨rfl, Option.some.inj h2⟩

/-! ## The ranges -/

/-- The bound of the one live klong (0, y) of a node: the node's own. -/
theorem single_bound (rn : KNode) (t : Time) (y : NodeId) (hi : Option Nat)
    (hy : (0, y) ∈ rn.liveAt t) (honly : ∀ c z, (c, z) ∈ rn.liveAt t → c = 0 ∧ z = y) :
    ((0, y), hi) ∈ childBounds (rn.liveAt t) hi := by
  apply childBounds_of_isNext _ hi (KNode.liveAt_order rn t) _ _ hy
  left
  refine ⟨rfl, ?_⟩
  intro r hr
  have := (honly r.1 r.2 hr).1
  simp only; omega

/-- The walk's ranges after the root r, inner with one live klong, the empty key
to y, gives way to y (N2 may hold anything at r). -/
theorem rangeOrder_collapseRoot (N1 N2 : NodeId → Option KNode) (t : Time) (r y : NodeId)
    (rn : KNode) (hR : RangeOrder N1 t r) (hT : TreeOK N1 t r) (hrn : N1 r = some rn)
    (hrl : rn.leaf = false) (hy : (0, y) ∈ rn.liveAt t)
    (honly : ∀ c z, (c, z) ∈ rn.liveAt t → c = 0 ∧ z = y)
    (hN2 : ∀ z, z ≠ r → N2 z = N1 z) : RangeOrder N2 t y := by
  have hy0 : ReachR N1 t r y 0 none := by
    have := ReachR.inner r rn 0 none 0 y none ReachR.root hrn hrl (single_bound rn t y none hy honly)
    simpa using this
  have hyr : y ≠ r := by
    intro h
    exact hT.no_self_link r 0 TReach.root ⟨rn, hrn, h ▸ hy⟩
  have hsub : ∀ z lo hi, ReachR N2 t y z lo hi → ReachR N1 t r z lo hi ∧ z ≠ r := by
    intro z lo hi h
    induction h with
    | root => exact ⟨hy0, hyr⟩
    | inner x n lo hi c z b _ hn hl hb ih =>
      obtain ⟨h1, h2⟩ := ih
      rw [hN2 x h2] at hn
      refine ⟨ReachR.inner x n lo hi c z b h1 hn hl hb, ?_⟩
      intro hzr
      exact hT.rootFree x c (reachR_tReach N1 t r x lo hi h1) ⟨n, hn, hzr ▸ childBounds_fst _ _ _ _ hb⟩
    | seg x n lo hi c z _ hn hl hc ih =>
      obtain ⟨h1, h2⟩ := ih
      rw [hN2 x h2] at hn
      refine ⟨ReachR.seg x n lo hi c z h1 hn hl hc, ?_⟩
      intro hzr
      exact hT.rootFree x c (reachR_tReach N1 t r x lo hi h1) ⟨n, hn, hzr ▸ hc⟩
  intro z lo hi m h hm
  obtain ⟨h1, h2⟩ := hsub z lo hi h
  rw [hN2 z h2] at hm
  exact hR z lo hi m h1 hm

/-- The walk's ranges after the segment root x below the segment leaf q, inner
with one live klong, the empty key to y, gives way to y: q's klong k1 names y
(N2 may hold anything at x). -/
theorem rangeOrder_segCollapse (N1 N2 : NodeId → Option KNode) (t : Time) (r q x y : NodeId)
    (qn qn2 xn : KNode) (k1 : Nat)
    (hR : RangeOrder N1 t r) (hT : TreeOK N1 t r)
    (hq : TReach N1 t r q) (hqn : N1 q = some qn) (hql : qn.leaf = true)
    (hk1 : (k1, x) ∈ qn.liveAt t) (hxn : N1 x = some xn) (hxl : xn.leaf = false)
    (hy : (0, y) ∈ xn.liveAt t) (honly : ∀ c z, (c, z) ∈ xn.liveAt t → c = 0 ∧ z = y)
    (hN2q : N2 q = some qn2) (hq2l : qn2.leaf = true)
    (hq2 : ∀ c z, (c, z) ∈ qn2.liveAt t → (c = k1 ∧ z = y) ∨ (c ≠ k1 ∧ (c, z) ∈ qn.liveAt t))
    (hN2 : ∀ z, z ≠ q → z ≠ x → N2 z = N1 z) : RangeOrder N2 t r := by
  have hxR : TReach N1 t r x := TReach.link hq ⟨qn, hqn, hk1⟩
  have hqx : q ≠ x := by
    intro h
    exact hT.no_self_link x k1 hxR ⟨qn, by rw [← h]; exact hqn, hk1⟩
  have hrx : r ≠ x := by
    intro h; exact hT.rootFree q k1 hq ⟨qn, hqn, h ▸ hk1⟩
  have hyx : y ≠ x := by
    intro h
    exact hT.no_self_link x 0 hxR ⟨xn, hxn, h ▸ hy⟩
  have honlyx : ∀ u c, TReach N1 t r u → TLink N1 t u c x → u = q ∧ c = k1 := fun u c hu hl =>
    hT.oneLink u c q k1 x hu hq hl ⟨qn, hqn, hk1⟩
  obtain ⟨qlo, qhi, hq0⟩ := reachR_of_reachS N1 t r q (tReach_reachS N1 t r q hq)
  have hx00 : ReachR N1 t r x 0 none := ReachR.seg q qn qlo qhi k1 x hq0 hqn hql hk1
  have hy00 : ReachR N1 t r y 0 none := by
    have := ReachR.inner x xn 0 none 0 y none hx00 hxn hxl (single_bound xn t y none hy honly)
    simpa using this
  let G : NodeId → Nat → Option Nat → Prop := fun z lo hi =>
    z ≠ x ∧ ∃ lo0 hi0, ReachR N1 t r z lo0 hi0 ∧ lo ≤ lo0 ∧ HiLE hi0 hi
  apply rangeOrder_of_good N2 t r G
  · exact ⟨hrx, 0, none, ReachR.root, Nat.le_refl _, HiLE.refl _⟩
  · intro z lo hi m c z' b _ hG hm hml hb
    obtain ⟨hzx, lo0, hi0, hz0, hlo, hhi⟩ := hG
    have hzq : z ≠ q := by intro h; rw [h, hN2q] at hm; cases hm; rw [hq2l] at hml; cases hml
    have hm0 : N1 z = some m := by rw [← hN2 z hzq hzx]; exact hm
    have hcz := childBounds_fst _ _ _ _ hb
    have hz'x : z' ≠ x := fun h =>
      hzq (honlyx z c (reachR_tReach N1 t r z lo0 hi0 hz0) ⟨m, hm0, h ▸ hcz⟩).1
    obtain ⟨lo1, hi1, h3, h4, h5⟩ := old_child_step N1 t r hR z m lo0 lo hi0 hi hz0 hm0 hml
      hlo hhi _ (KNode.liveAt_order m t) c z' z' b hcz hb
      (fun r' hr' hlt => ⟨r', hr', hlt, Nat.le_refl _⟩)
    exact ⟨hz'x, lo1, hi1, h3, h4, h5⟩
  · intro z lo hi m c z' _ hG hm hml hcz
    obtain ⟨hzx, lo0, hi0, hz0, _, _⟩ := hG
    by_cases hzq : z = q
    · rw [hzq, hN2q] at hm; cases hm
      rw [hzq] at hz0
      rcases hq2 c z' hcz with ⟨_, h2⟩ | ⟨h1, h2⟩
      · rw [h2]; exact ⟨hyx, 0, none, hy00, Nat.le_refl _, HiLE.refl _⟩
      · have hz'x : z' ≠ x := fun h => h1 (honlyx q c hq ⟨qn, hqn, h ▸ h2⟩).2
        exact ⟨hz'x, 0, none, ReachR.seg q qn lo0 hi0 c z' hz0 hqn hql h2, Nat.le_refl _,
          HiLE.refl _⟩
    · have hm0 : N1 z = some m := by rw [← hN2 z hzq hzx]; exact hm
      have hz'x : z' ≠ x := fun h =>
        hzq (honlyx z c (reachR_tReach N1 t r z lo0 hi0 hz0) ⟨m, hm0, h ▸ hcz⟩).1
      exact ⟨hz'x, 0, none, ReachR.seg z m lo0 hi0 c z' hz0 hm0 hml hcz, Nat.le_refl _,
        HiLE.refl _⟩
  · intro z lo hi m _ hG hm
    obtain ⟨hzx, lo0, hi0, hz0, hlo, hhi⟩ := hG
    by_cases hzq : z = q
    · rw [hzq, hN2q] at hm; cases hm
      rw [hzq] at hz0
      refine nodeRange_sub qn qn2 t lo0 lo hi0 hi (hR q lo0 hi0 qn hz0 hqn) (by rw [hq2l, hql]) ?_
        hlo hhi
      intro q' hq'
      rcases hq2 q'.1 q'.2 hq' with ⟨h1, _⟩ | ⟨_, h2⟩
      · exact ⟨(k1, x), hk1, h1.symm⟩
      · exact ⟨q', h2, rfl⟩
    · have hm0 : N1 z = some m := by rw [← hN2 z hzq hzx]; exact hm
      exact nodeRange_wider m t lo0 lo hi0 hi (hR z lo0 hi0 m hz0 hm0) hlo hhi

end SIS.Tree
