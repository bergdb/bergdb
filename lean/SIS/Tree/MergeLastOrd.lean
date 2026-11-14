import SIS.Tree.GetMergeAny
import SIS.Tree.MergeGOrd

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! The order of the merge's full parent's last version below an inner parent
(bergdb 024-12, case (4); `LastOrd` for the reach back of
`writerWP_handleFull_lastVF2`): from the walk's ranges (`RangeOrder`), the last
version's live compare values are 0 or above the parent's klong to it. -/

theorem MergeGOrd.toGOK {ln rn : KNode} {cR : Nat} {m2 : Option (NodeId × Nat)} {t : Time}
    (h : MergeGOrd ln rn cR m2 t) : MergeGOK ln rn cR m2 t := by
  intro y g hm
  rcases (h y g hm).2 with h1 | h1 | ⟨h1, _⟩
  · exact Or.inl h1
  · exact Or.inr (Or.inr h1)
  · exact Or.inr (Or.inl h1)

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

/-- A last version of a node p below an inner node q whose compare values are
p's live ones is ordered as `LastOrd` asks, from the walk's ranges: at or above
q's klong K to p for a segment leaf, 0 or above it for an inner node. -/
theorem lastOrd_raw_of_live (c : Ctx) (N : NodeId → Option KNode) (root : NodeId)
    (hR : RangeOrder N c.i root) (q : NodeId) (qn : KNode) (K : Nat) (p : NodeId) (pn : KNode)
    (hq : TReach N c.i root q) (hqn : N q = some qn) (hql : qn.leaf = false)
    (hK : (K, p) ∈ qn.liveAt c.i) (hpn : N p = some pn)
    (hpt : ∀ s, Klong.time s ∈ pn.ks → s ≤ c.i) (last : KNode)
    (hsub : ∀ c' z, (c', z) ∈ (⟨pn.leaf, last.ks⟩ : KNode).live → ∃ z', (c', z') ∈ pn.live) :
    ∀ c' z, (c', z) ∈ (⟨pn.leaf, last.ks⟩ : KNode).live →
      if pn.leaf = true then K ≤ c' else (c' = 0 ∨ K < c') := by
  obtain ⟨hP1, _⟩ := mrg_child_range N c.i root hR q qn (tReach_reachS N c.i root q hq) hqn hql
    K p pn hK hpn
  intro c' z hz
  obtain ⟨z', hz'⟩ := hsub c' z hz
  have hm : (c', z') ∈ pn.liveAt c.i := by rw [KNode.liveAt_of_times pn c.i hpt]; exact hz'
  obtain ⟨ha, hb⟩ := hP1 c' z' hm
  cases hpl : pn.leaf
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rcases hb hpl with h | h
    · exact Or.inl h
    · rcases Nat.eq_zero_or_pos K with hK0 | hK0
      · rcases Nat.eq_zero_or_pos c' with h0 | h0
        · exact Or.inl h0
        · exact Or.inr (by omega)
      · exact Or.inr (h hK0)
  · simp only [↓reduceIte]
    rcases Nat.eq_zero_or_pos K with hK0 | hK0
    · omega
    · exact ha hpl hK0

end SIS.Tree
