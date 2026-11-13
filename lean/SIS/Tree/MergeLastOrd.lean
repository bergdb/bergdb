import SIS.Tree.GetMergeAny

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! The order of the merge's full parent's last version below an inner parent
(bergdb 024-12, case (4); `LastOrd` for the reach back of
`writerWP_handleFull_lastVF2`): from the walk's ranges (`RangeOrder`), the last
version's live compare values are 0 or above the parent's klong to it. -/

/-- `MergeGOK` with the order of the second node's compare value g: g is
positive, and when it is a live compare value of the left node, another one of
the left node is below it. -/
def MergeGOrd (ln rn : KNode) (cR : Nat) (m2 : Option (NodeId × Nat)) (t : Time) : Prop :=
  ∀ y g, m2 = some (y, g) → 0 < g ∧ (g = cR ∨ (∃ z, (g, z) ∈ rn.liveAt t) ∨
    ((∃ z, (g, z) ∈ ln.liveAt t) ∧ ∃ c0 z0, (c0, z0) ∈ ln.liveAt t ∧ c0 < g))

theorem MergeGOrd.toGOK {ln rn : KNode} {cR : Nat} {m2 : Option (NodeId × Nat)} {t : Time}
    (h : MergeGOrd ln rn cR m2 t) : MergeGOK ln rn cR m2 t := by
  intro y g hm
  rcases (h y g hm).2 with h1 | h1 | ⟨h1, _⟩
  · exact Or.inl h1
  · exact Or.inr (Or.inr h1)
  · exact Or.inr (Or.inl h1)

/-- `MergeGOrd` for the merge's two nodes: g heads the second half of the
sorted merged klongs (`mrg_splitMerged_two`), so the first merged klong is below
it. -/
theorem mergeGOrd_two (inner : Bool) (ln rn : KNode) (t : Time) (cR h g : Nat) (yg m : NodeId)
    (hlt : ∀ s, Klong.time s ∈ ln.ks → s ≤ t) (hrt : ∀ s, Klong.time s ∈ rn.ks → s ≤ t)
    (hs : CvSorted (mergeList inner cR ln.live rn.live)) (hh : 1 ≤ h)
    (hgs : ((mergeList inner cR ln.live rn.live).drop h).head? = some (g, yg)) :
    MergeGOrd ln rn cR (some (m, g)) t := by
  intro y g' hyg
  simp only [Option.some.injEq, Prod.mk.injEq] at hyg
  obtain ⟨_, hgg⟩ := hyg
  rw [← hgg]
  have hmemD : (g, yg) ∈ (mergeList inner cR ln.live rn.live).drop h := List.mem_of_mem_head? hgs
  have hmem : (g, yg) ∈ mergeList inner cR ln.live rn.live := List.mem_of_mem_drop hmemD
  -- the first merged klong is below g
  obtain ⟨a, rest, hal⟩ : ∃ a rest, mergeList inner cR ln.live rn.live = a :: rest := by
    cases hm : mergeList inner cR ln.live rn.live with
    | nil => rw [hm] at hmem; cases hmem
    | cons a rest => exact ⟨a, rest, rfl⟩
  have hag : a.1 < g := by
    rw [hal] at hs hmemD
    obtain ⟨h', rfl⟩ : ∃ h', h = h' + 1 := ⟨h - 1, by omega⟩
    simp only [List.drop_succ_cons] at hmemD
    exact (List.pairwise_cons.mp hs).1 _ (List.mem_of_mem_drop hmemD)
  refine ⟨by omega, ?_⟩
  rcases mem_mergeList inner cR ln.live rn.live g yg hmem with h1 | h1 | ⟨c0, h0, hc0⟩
  · refine Or.inr (Or.inr ⟨⟨yg, by rw [KNode.liveAt_of_times ln t hlt]; exact h1⟩, ?_⟩)
    have ha : a ∈ ln.live := by
      cases hl : ln.live with
      | nil => rw [hl] at h1; cases h1
      | cons b bs =>
        unfold mergeList at hal
        rw [hl] at hal
        simp only [List.cons_append, List.cons.injEq] at hal
        rw [← hal.1]; exact List.mem_cons_self
    exact ⟨a.1, a.2, by rw [KNode.liveAt_of_times ln t hlt]; exact ha, hag⟩
  · exact Or.inr (Or.inl ⟨yg, by
      rw [KNode.liveAt_of_times rn t hrt]; exact List.mem_of_mem_tail h1⟩)
  · cases inner
    · simp only [Bool.false_eq_true, ↓reduceIte] at hc0
      exact Or.inr (Or.inl ⟨yg, by
        rw [KNode.liveAt_of_times rn t hrt, hc0]; exact List.mem_of_mem_head? h0⟩)
    · simp only [↓reduceIte] at hc0
      exact Or.inl hc0

/-- The lower bound of a node y two links below an inner node q, through q's
klong K to an inner node x (the walk's ranges): a segment leaf y's live compare
values are at or above K, an inner y's are 0 or above K. -/
theorem rangeG2_low (N : NodeId → Option KNode) (t : Time) (root : NodeId)
    (hR : RangeOrder N t root) (q : NodeId) (qn : KNode) (K : Nat) (x : NodeId) (xn : KNode)
    (Ky : Nat) (y : NodeId) (yn : KNode)
    (hq : ReachS N t root q) (hqn : N q = some qn) (hql : qn.leaf = false)
    (hK : (K, x) ∈ qn.liveAt t) (hxn : N x = some xn) (hxl : xn.leaf = false)
    (hKy : (Ky, y) ∈ xn.liveAt t) (hyn : N y = some yn) :
    ∀ cc z, (cc, z) ∈ yn.liveAt t → (yn.leaf = true → K ≤ cc) ∧ (yn.leaf = false → cc = 0 ∨ K < cc) := by
  obtain ⟨lo, hi, hqr⟩ := reachR_of_reachS N t root q hq
  obtain ⟨b, hb⟩ := childBounds_exists (qn.liveAt t) hi (K, x) hK
  have hxr := ReachR.inner q qn lo hi K x b hqr hqn hql hb
  have hxrange := hR x _ b xn hxr hxn
  obtain ⟨b', hb'⟩ := childBounds_exists (xn.liveAt t) b (Ky, y) hKy
  have hyr := ReachR.inner x xn _ b Ky y b' hxr hxn hxl hb'
  have hyrange := hR y _ b' yn hyr hyn
  have hlox : K ≤ (if K == 0 then lo else K) := by
    by_cases h0 : K = 0
    · omega
    · have hb0 : (K == 0) = false := by simpa using h0
      simp only [hb0, Bool.false_eq_true, ↓reduceIte, Nat.le_refl]
  have hloy : K ≤ (if Ky == 0 then (if K == 0 then lo else K) else Ky) := by
    by_cases hy0 : Ky = 0
    · have hb0 : (Ky == 0) = true := by simpa using hy0
      simp only [hb0, ↓reduceIte]
      exact hlox
    · have hb0 : (Ky == 0) = false := by simpa using hy0
      simp only [hb0, Bool.false_eq_true, ↓reduceIte]
      obtain ⟨hlx, _⟩ := hxrange (Ky, y) hKy
      dsimp only at hlx
      simp only [hxl, Bool.false_eq_true, ↓reduceIte] at hlx
      omega
  intro cc z hz
  obtain ⟨hlow, _⟩ := hyrange (cc, z) hz
  dsimp only at hlow
  refine ⟨fun hyl => ?_, fun hyl => ?_⟩
  · simp only [hyl, ↓reduceIte] at hlow
    omega
  · simp only [hyl, Bool.false_eq_true, ↓reduceIte] at hlow
    omega

/-- The merge's full parent's last version below an inner parent q is ordered
(`LastOrd`'s conclusion for an inner parent node pn): its live compare values
are 0 or above q's klong K to it, from the walk's ranges and `MergeGOrd`. -/
theorem mergeLast_ord (c : Ctx) (N : NodeId → Option KNode) (root : NodeId)
    (hR : RangeOrder N c.i root) (q : NodeId) (qn : KNode) (K : Nat) (p : NodeId) (pn : KNode)
    (hq : TReach N c.i root q) (hqn : N q = some qn) (hql : qn.leaf = false)
    (hK : (K, p) ∈ qn.liveAt c.i) (hpn : N p = some pn) (hpl : pn.leaf = false)
    (hpt : ∀ s, Klong.time s ∈ pn.ks → s ≤ c.i)
    (cL cR : Nat) (l r : NodeId) (ln rn : KNode) (hclt : cL < cR)
    (hpL : (cL, l) ∈ pn.liveAt c.i) (hpR : (cR, r) ∈ pn.liveAt c.i)
    (hln : N l = some ln) (hrn : N r = some rn) (m1 : NodeId) (m2 : Option (NodeId × Nat))
    (last : KNode) (hlast : mergeFullLast pn c.i cL m1 cR m2 = some last)
    (hg : MergeGOrd ln rn cR m2 c.i) :
    ∀ c' z, (c', z) ∈ (⟨pn.leaf, last.ks⟩ : KNode).live → c' = 0 ∨ K < c' := by
  have hqS := tReach_reachS N c.i root q hq
  obtain ⟨hP1, _⟩ := mrg_child_range N c.i root hR q qn hqS hqn hql K p pn hK hpn
  have hP : ∀ cc z, (cc, z) ∈ pn.liveAt c.i → cc = 0 ∨ K < cc := by
    intro cc z hz
    rcases (hP1 cc z hz).2 hpl with h | h
    · exact Or.inl h
    · rcases Nat.eq_zero_or_pos K with hK0 | hK0
      · rcases Nat.eq_zero_or_pos cc with h0 | h0
        · exact Or.inl h0
        · exact Or.inr (by omega)
      · exact Or.inr (h hK0)
  obtain ⟨htl, hleafl, hnone, hsome⟩ := mergeFullLast_liveAt pn c.i cL m1 cR m2 last hlast hpt
  have hlasteq : (⟨pn.leaf, last.ks⟩ : KNode) = last := by
    cases last with
    | mk lf ks => simp only at hleafl; rw [hleafl]
  intro c' z hz
  rw [hlasteq] at hz
  have hz' : (c', z) ∈ last.liveAt c.i := by rw [KNode.liveAt_of_times last c.i htl]; exact hz
  cases hm2 : m2 with
  | none =>
    rcases hnone hm2 c' z hz' with ⟨hc, _⟩ | ⟨hm, _, _⟩
    · rw [hc]; exact hP cL l hpL
    · exact hP c' z hm
  | some yg =>
    obtain ⟨y, g⟩ := yg
    rcases hsome y g hm2 c' z hz' with ⟨hc, _⟩ | ⟨hc, _⟩ | ⟨hm, _, _⟩
    · rw [hc]; exact hP cL l hpL
    · rw [hc]
      obtain ⟨hg0, hgw⟩ := hg y g hm2
      have hKR : K < cR := by
        rcases hP cR r hpR with h | h
        · omega
        · exact h
      rcases hgw with hgc | ⟨z1, hz1⟩ | ⟨⟨z1, hz1⟩, c0, z0, hc0, hc0g⟩
      · rw [hgc]; exact Or.inr hKR
      · obtain ⟨hr1, _⟩ := mrg_child_range N c.i root hR p pn (ReachS.step q qn K p hqS hqn hK) hpn hpl
          cR r rn hpR hrn
        obtain ⟨hra, hrb⟩ := hr1 g z1 hz1
        cases hrl : rn.leaf
        · rcases hrb hrl with h | h
          · omega
          · exact Or.inr (by have := h (by omega); omega)
        · exact Or.inr (by have := hra hrl (by omega); omega)
      · have hlow := rangeG2_low N c.i root hR q qn K p pn cL l ln hqS hqn hql hK hpn hpl hpL hln
        cases hll : ln.leaf
        · rcases (hlow g z1 hz1).2 hll with h | h
          · omega
          · exact Or.inr h
        · have := (hlow c0 z0 hc0).1 hll
          exact Or.inr (by omega)
    · exact hP c' z hm

/-- `LastOrd` for an inner node at depth D + 1 whose last version is ordered. -/
theorem lastOrd_of_inner (c : Ctx) (K : Nat → Nat) (Nn : Nat → KNode) (D : Nat) (last : KNode)
    (hpl : (Nn (D + 1)).leaf = false)
    (h : ∀ c' z, (c', z) ∈ (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode).live → c' = 0 ∨ K (D + 1) < c') :
    LastOrd c K Nn D last := by
  intro _ _ c' z hz
  simp only [hpl, Bool.false_eq_true, ↓reduceIte]
  exact h c' z hz

end SIS.Tree
