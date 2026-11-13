/-
The take-back's (B), (C) and their node facts through the new segments of a put
(bergdb 024-12, TP7, case (3); `J2N`). A new segment leaf is empty between its
making and the next step, so it does not start at t yet: `J2NE` is `J2N` but for
one empty leaf x, reached, which may be no node of the transaction's time.
Each step gives x a klong of t to the next new leaf (`j2NE_step`), the last
step a klong to the put's value (`j2N_last`); the first comes from the leaf of
the prefix with room (`j2NE_start`).
-/
import SIS.Tree.TakeDeadAssembly

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- `J2N` with one empty leaf x, reached, exempt from `MadeStartN`. -/
def J2NE (N : NodeId → Option KNode) (t : Time) (r B : NodeId) (vals : List NodeId) (x : NodeId) : Prop :=
  TtReachedN N t r ∧ DeadLiveN N t B vals ∧ OldBelowN N t B ∧ OldStartN N t B ∧
    (∀ q qn, N q = some qn → B ≤ q → q ≠ x → qn.firstTime = some t) ∧ ValsNoNodeN N vals ∧
    N x = some ⟨true, []⟩ ∧ TReach N t r x ∧ B ≤ x

theorem empty_add (t : Time) (k : Klong) : (⟨true, []⟩ : KNode).add t k = ⟨true, [.time t, k]⟩ := rfl

theorem single_facts (t : Time) (a : Nat) (y : NodeId) (hpos : 0 < t) (B : NodeId)
    (vals : List NodeId) :
    DeadLiveK ⟨true, [.time t, .key a y]⟩ t B vals ∧
    prefixAt [.time t, .key a y] (t - 1) = [] ∧ (⟨true, [.time t, .key a y]⟩ : KNode).firstTime = some t ∧
    (a, y) ∈ (⟨true, [.time t, .key a y]⟩ : KNode).liveAt t := by
  have hls : LastShaped t ⟨true, [.time t, .key a y]⟩ := ⟨[(a, y)], rfl, by simp⟩
  obtain ⟨hD, hp, hf⟩ := lastShaped_facts t _ hls hpos B vals
  refine ⟨hD, hp, hf, ?_⟩
  have := (mrg_newKlongs_liveAt_iff true t [(a, y)] (by simp) a y).mpr (by simp)
  exact this

/-- A step: the empty leaf x gets a klong of t to a new empty leaf x'. -/
theorem j2NE_step (N N' : NodeId → Option KNode) (t : Time) (r B : NodeId) (vals : List NodeId)
    (x x' : NodeId) (a : Nat) (hpos : 0 < t) (hJ : J2NE N t r B vals x) (hx'N : N x' = none)
    (hx'B : B ≤ x') (hx'v : x' ∉ vals)
    (hN'x : N' x = some ⟨true, [.time t, .key a x']⟩) (hN'x' : N' x' = some ⟨true, []⟩)
    (hother : ∀ z, z ≠ x → z ≠ x' → N' z = N z) : J2NE N' t r B vals x' := by
  obtain ⟨hTt, hD, hO, hS, hM, hV, hNx, hxR, hxB⟩ := hJ
  obtain ⟨hDx, hpx, hfx, hlx⟩ := single_facts t a x' hpos B vals
  -- what N reaches N' reaches, but through x, which has no live klong in N
  have hxlive : ∀ c z, (c, z) ∉ (⟨true, []⟩ : KNode).liveAt t := by
    intro c z h
    exact absurd (KNode.liveAt_key_mem _ t c z h) (by simp)
  have hreach : ∀ u, TReach N t r u → TReach N' t r u := by
    intro u hu
    induction hu with
    | root => exact TReach.root
    | @link a0 c u ha hl ih =>
      obtain ⟨an, han, hau⟩ := hl
      by_cases hax : a0 = x
      · rw [hax, hNx] at han; cases han; exact absurd hau (hxlive c u)
      · have hax' : a0 ≠ x' := fun he => by rw [he, hx'N] at han; cases han
        exact TReach.link ih ⟨an, by rw [hother a0 hax hax']; exact han, hau⟩
  have hxR' : TReach N' t r x := hreach x hxR
  have hx'R : TReach N' t r x' := TReach.link hxR' ⟨_, hN'x, hlx⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hN'x', hx'R, hx'B⟩
  · intro u un hu hm
    by_cases hux : u = x
    · rw [hux]; exact hxR'
    · by_cases hux' : u = x'
      · rw [hux'] at hu ⊢; rw [hN'x'] at hu; cases hu; simp at hm
      · rw [hother u hux hux'] at hu; exact hreach u (hTt u un hu hm)
  · intro u un hu
    by_cases hux : u = x
    · rw [hux, hN'x] at hu; cases hu; exact hDx
    · by_cases hux' : u = x'
      · rw [hux', hN'x'] at hu; cases hu
        intro i cv y hi; simp at hi
      · rw [hother u hux hux'] at hu; exact hD u un hu
  · intro u un hu cv y hk
    by_cases hux : u = x
    · rw [hux, hN'x] at hu; cases hu; simp only at hk; rw [hpx] at hk; cases hk
    · by_cases hux' : u = x'
      · rw [hux', hN'x'] at hu; cases hu; simp [prefixAt] at hk
      · rw [hother u hux hux'] at hu; exact hO u un hu cv y hk
  · intro u un hu huB
    by_cases hux : u = x
    · rw [hux] at huB; omega
    · by_cases hux' : u = x'
      · rw [hux'] at huB; omega
      · rw [hother u hux hux'] at hu; exact hS u un hu huB
  · intro u un hu huB hux'
    by_cases hux : u = x
    · rw [hux, hN'x] at hu; cases hu; exact hfx
    · rw [hother u hux hux'] at hu; exact hM u un hu huB hux
  · intro y hy
    by_cases hyx : y = x
    · rw [hyx] at hy; rw [hV x hy] at hNx; cases hNx
    · by_cases hyx' : y = x'
      · rw [hyx'] at hy; exact absurd hy hx'v
      · rw [hother y hyx hyx']; exact hV y hy

/-- The last step: the empty leaf x gets a klong of t to the put's value v. -/
theorem j2N_last (N N' : NodeId → Option KNode) (t : Time) (r B : NodeId) (vals : List NodeId)
    (x v : NodeId) (a : Nat) (hpos : 0 < t) (hJ : J2NE N t r B vals x) (hvN : N' v = none)
    (hN'x : N' x = some ⟨true, [.time t, .key a v]⟩)
    (hother : ∀ z, z ≠ x → N' z = N z) : J2N N' t r B (vals ++ [v]) := by
  obtain ⟨hTt, hD, hO, hS, hM, hV, hNx, hxR, hxB⟩ := hJ
  obtain ⟨hDx, hpx, hfx, _⟩ := single_facts t a v hpos B (vals ++ [v])
  have hxlive : ∀ c z, (c, z) ∉ (⟨true, []⟩ : KNode).liveAt t := by
    intro c z h
    exact absurd (KNode.liveAt_key_mem _ t c z h) (by simp)
  have hreach : ∀ u, TReach N t r u → TReach N' t r u := by
    intro u hu
    induction hu with
    | root => exact TReach.root
    | @link a0 c u ha hl ih =>
      obtain ⟨an, han, hau⟩ := hl
      by_cases hax : a0 = x
      · rw [hax, hNx] at han; cases han; exact absurd hau (hxlive c u)
      · exact TReach.link ih ⟨an, by rw [hother a0 hax]; exact han, hau⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro u un hu hm
    by_cases hux : u = x
    · rw [hux]; exact hreach x hxR
    · rw [hother u hux] at hu; exact hreach u (hTt u un hu hm)
  · intro u un hu
    by_cases hux : u = x
    · rw [hux, hN'x] at hu; cases hu; exact hDx
    · rw [hother u hux] at hu
      intro i cv y hi hB hv
      exact hD u un hu i cv y hi hB (fun h => hv (List.mem_append_left _ h))
  · intro u un hu cv y hk
    by_cases hux : u = x
    · rw [hux, hN'x] at hu; cases hu; simp only at hk; rw [hpx] at hk; cases hk
    · rw [hother u hux] at hu; exact hO u un hu cv y hk
  · intro u un hu huB
    by_cases hux : u = x
    · rw [hux] at huB; omega
    · rw [hother u hux] at hu; exact hS u un hu huB
  · intro u un hu huB
    by_cases hux : u = x
    · rw [hux, hN'x] at hu; cases hu; exact hfx
    · rw [hother u hux] at hu; exact hM u un hu huB hux
  · intro y hy
    rcases List.mem_append.mp hy with h | h
    · by_cases hyx : y = x
      · rw [hyx] at h; rw [hV x h] at hNx; cases hNx
      · rw [hother y hyx]; exact hV y h
    · rw [List.mem_singleton.mp h]; exact hvN

/-- The first step: the leaf cur of the prefix, reached, with no live klong of
c0, gets a klong of t to a new empty leaf child. -/
theorem j2NE_start (N N' : NodeId → Option KNode) (t : Time) (r B : NodeId) (vals : List NodeId)
    (cur child : NodeId) (cn : KNode) (c0 : Nat) (hpos : 0 < t) (hJ : J2N N t r B vals)
    (hcur : N cur = some cn) (hcR : TReach N t r cur) (hw : klongsWf cn.ks = true)
    (ht : ∀ s, Klong.time s ∈ cn.ks → s ≤ t) (hc0 : ∀ z, (c0, z) ∉ cn.liveAt t)
    (hchN : N child = none) (hchB : B ≤ child) (hchv : child ∉ vals)
    (hN'c : N' cur = some (cn.add t (.key c0 child))) (hN'ch : N' child = some ⟨true, []⟩)
    (hother : ∀ z, z ≠ cur → z ≠ child → N' z = N z) : J2NE N' t r B vals child := by
  obtain ⟨hTt, hD, hO, hS, hM, hV⟩ := hJ
  have hcc : cur ≠ child := fun he => by rw [he, hchN] at hcur; cases hcur
  have hreach : ∀ u, TReach N t r u → TReach N' t r u := by
    intro u hu
    induction hu with
    | root => exact TReach.root
    | @link a0 c u ha hl ih =>
      obtain ⟨an, han, hau⟩ := hl
      by_cases hax : a0 = cur
      · rw [hax, hcur] at han; cases han
        have hcne : c ≠ c0 := fun he => hc0 u (he ▸ hau)
        rw [hax] at ih
        exact TReach.link ih ⟨_, hN'c, KNode.add_liveAt_keep cn c0 child t hw ht c u hau hcne⟩
      · have hax' : a0 ≠ child := fun he => by rw [he, hchN] at han; cases han
        exact TReach.link ih ⟨an, by rw [hother a0 hax hax']; exact han, hau⟩
  have hcR' := hreach cur hcR
  have hchR : TReach N' t r child := TReach.link hcR' ⟨_, hN'c, KNode.add_liveAt_new cn c0 child t hw ht⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hN'ch, hchR, hchB⟩
  · intro u un hu hm
    by_cases huc : u = cur
    · rw [huc]; exact hcR'
    · by_cases huch : u = child
      · rw [huch] at hu; rw [hN'ch] at hu; cases hu; simp at hm
      · rw [hother u huc huch] at hu; exact hreach u (hTt u un hu hm)
  · intro u un hu
    by_cases huc : u = cur
    · rw [huc, hN'c] at hu; cases hu
      exact deadLiveK_addKey cn t B vals c0 child hw ht (deadLiveK_of_N N t B vals hD cur cn hcur)
        (fun z hz => absurd hz (hc0 z))
    · by_cases huch : u = child
      · rw [huch, hN'ch] at hu; cases hu
        intro i cv y hi; simp at hi
      · rw [hother u huc huch] at hu; exact hD u un hu
  · intro u un hu cv y hk
    by_cases huc : u = cur
    · rw [huc, hN'c] at hu; cases hu
      rw [KNode.prefixAt_add cn t _ hpos] at hk; exact hO cur cn hcur cv y hk
    · by_cases huch : u = child
      · rw [huch, hN'ch] at hu; cases hu; simp [prefixAt] at hk
      · rw [hother u huc huch] at hu; exact hO u un hu cv y hk
  · intro u un hu huB
    by_cases huc : u = cur
    · rw [huc, hN'c] at hu; cases hu
      obtain ⟨s, hs, hf⟩ := hS cur cn hcur (by rw [← huc]; exact huB)
      exact ⟨s, hs, KNode.firstTime_add_some cn t _ s hf⟩
    · by_cases huch : u = child
      · rw [huch] at huB; omega
      · rw [hother u huc huch] at hu; exact hS u un hu huB
  · intro u un hu huB huch
    by_cases huc : u = cur
    · rw [huc, hN'c] at hu; cases hu
      exact KNode.firstTime_add_some cn t _ t (hM cur cn hcur (by rw [← huc]; exact huB))
    · rw [hother u huc huch] at hu; exact hM u un hu huB
  · intro y hy
    by_cases hyc : y = cur
    · rw [hyc] at hy; rw [hV cur hy] at hcur; cases hcur
    · by_cases hych : y = child
      · rw [hych] at hy; exact absurd hy hchv
      · rw [hother y hyc hych]; exact hV y hy

end SIS.Tree
