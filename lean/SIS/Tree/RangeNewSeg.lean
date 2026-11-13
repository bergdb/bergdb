import SIS.Tree.RangeOps

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! A put that makes a new segment keeps the walk's ranges (bergdb 024-12, TP10;
`RangeOrder`): the leaf L of the key's segment gets a klong to a new segment
leaf y, which a segment's whole range takes, and y holds a klong to the value
(`rangeOrder_leafAddNew`, `rangeOrder_put_newSeg`). -/

/-- The walk's ranges after the leaf L gets a klong (cv, y) to a new leaf y,
cv in L's range, whose live klongs name no node. -/
theorem rangeOrder_leafAddNew (N N' : NodeId → Option KNode) (t : Time) (r L y : NodeId)
    (n m yn : KNode) (cv : Nat) (hR : RangeOrder N t r) (hn : N L = some n) (hnl : n.leaf = true)
    (hN'L : N' L = some m) (hml : m.leaf = true)
    (hmlive : ∀ c z, (c, z) ∈ m.liveAt t → (c = cv ∧ z = y) ∨ (c, z) ∈ n.liveAt t)
    (hcv : ∀ lo hi, ReachR N t r L lo hi → lo ≤ cv ∧ UpperBound hi cv)
    (hy : N y = none) (hry : r ≠ y) (hyfree : ∀ u c, TReach N t r u → ¬ TLink N t u c y)
    (hN'y : N' y = some yn) (hynl : yn.leaf = true)
    (hynk : ∀ c z, (c, z) ∈ yn.liveAt t → N' z = none)
    (hN' : ∀ z, z ≠ L → z ≠ y → N' z = N z) : RangeOrder N' t r := by
  have hyL : y ≠ L := by intro h; rw [h, hn] at hy; cases hy
  have hold : ∀ z m', N' z = some m' → z ≠ L → z ≠ y → N z = some m' := by
    intro z m' h h1 h2; rw [← hN' z h1 h2]; exact h
  let G : NodeId → Nat → Option Nat → Prop := fun z lo hi =>
    (z ≠ y ∧ ∃ lo0 hi0, ReachR N t r z lo0 hi0 ∧ lo ≤ lo0 ∧ HiLE hi0 hi) ∨
    (z = y ∧ lo = 0 ∧ hi = none) ∨ N' z = none
  apply rangeOrder_of_good N' t r G
  · exact Or.inl ⟨hry, 0, none, ReachR.root, Nat.le_refl _, HiLE.refl _⟩
  · intro z lo hi m' c z' b _ hG hm hml' hb
    rcases hG with ⟨hzy, lo0, hi0, hz0, hlo, hhi⟩ | ⟨hzy, _, _⟩ | hG
    · have hzL : z ≠ L := by intro h; rw [h, hN'L] at hm; cases hm; rw [hml] at hml'; cases hml'
      have hm0 := hold z m' hm hzL hzy
      have hcz := childBounds_fst _ _ _ _ hb
      have hz'y : z' ≠ y := fun h =>
        hyfree z c (reachR_tReach N t r z lo0 hi0 hz0) ⟨m', hm0, h ▸ hcz⟩
      obtain ⟨lo1, hi1, h3, h4, h5⟩ := old_child_step N t r hR z m' lo0 lo hi0 hi hz0 hm0 hml' hlo hhi
        _ (KNode.liveAt_order m' t) c z' z' b hcz hb (fun r' hr' hlt => ⟨r', hr', hlt, Nat.le_refl _⟩)
      exact Or.inl ⟨hz'y, lo1, hi1, h3, h4, h5⟩
    · rw [hzy, hN'y] at hm; cases hm; rw [hynl] at hml'; cases hml'
    · rw [hG] at hm; cases hm
  · intro z lo hi m' c z' _ hG hm hml' hcz
    rcases hG with ⟨hzy, lo0, hi0, hz0, _, _⟩ | ⟨hzy, _, _⟩ | hG
    · by_cases hzL : z = L
      · rw [hzL, hN'L] at hm; cases hm
        rw [hzL] at hz0
        rcases hmlive c z' hcz with ⟨_, h2⟩ | h2
        · rw [h2]; exact Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)
        · have hz'y : z' ≠ y := fun h =>
            hyfree L c (reachR_tReach N t r L lo0 hi0 hz0) ⟨n, hn, h ▸ h2⟩
          exact Or.inl ⟨hz'y, 0, none, ReachR.seg L n lo0 hi0 c z' hz0 hn hnl h2, Nat.le_refl _,
            HiLE.refl _⟩
      · have hm0 := hold z m' hm hzL hzy
        have hz'y : z' ≠ y := fun h =>
          hyfree z c (reachR_tReach N t r z lo0 hi0 hz0) ⟨m', hm0, h ▸ hcz⟩
        exact Or.inl ⟨hz'y, 0, none, ReachR.seg z m' lo0 hi0 c z' hz0 hm0 hml' hcz, Nat.le_refl _,
          HiLE.refl _⟩
    · rw [hzy, hN'y] at hm; cases hm
      exact Or.inr (Or.inr (hynk c z' hcz))
    · rw [hG] at hm; cases hm
  · intro z lo hi m' _ hG hm
    rcases hG with ⟨hzy, lo0, hi0, hz0, hlo, hhi⟩ | ⟨hzy, hlo, hhi⟩ | hG
    · by_cases hzL : z = L
      · rw [hzL, hN'L] at hm; cases hm
        rw [hzL] at hz0
        obtain ⟨hcl, hcu⟩ := hcv lo0 hi0 hz0
        intro q hq
        simp only [hml, ↓reduceIte]
        rcases hmlive q.1 q.2 hq with ⟨h1, _⟩ | h1
        · rw [h1]; exact ⟨by omega, upperBound_of_hiLE hi0 hi cv hhi hcu⟩
        · obtain ⟨h3, h4⟩ := hR L lo0 hi0 n hz0 hn q h1
          simp only [hnl, ↓reduceIte] at h3
          exact ⟨by omega, upperBound_of_hiLE hi0 hi q.1 hhi h4⟩
      · exact nodeRange_wider m' t lo0 lo hi0 hi (hR z lo0 hi0 m' hz0 (hold z m' hm hzL hzy)) hlo hhi
    · rw [hzy, hN'y] at hm; cases hm
      rw [hhi]
      intro q _
      simp only [hynl, ↓reduceIte]
      exact ⟨by omega, trivial⟩
    · rw [hG] at hm; cases hm

/-- A put of a key one segment below a leaf with room for the new klong, the
segment not there (`writerWP_put_newSeg_after`), keeps the walk's ranges. -/
theorem rangeOrder_put_newSeg (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (pre : List Nat) (c0 cl h : Nat) (rk0 : NodeId) (w : W) (hI : PutInv c base w)
    (hR : RangeOrder (wNode c.p base w) c.i w.top.rootKey) (hM : 2 ≤ c.p.M)
    (hrk : segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk0)
    (hcur : ∀ L n, (L, c0) ∈ eqVisits (wNode c.p base w) c.i c0 c.p.fuel rk0 →
      wNode c.p base w L = some n → n.leaf = true →
      n.searchEq c.i c0 = none ∧ n.size + 1 < c.p.M) :
    WriterWP (putKv (.put (pre ++ [c0, cl]) h)) c w (fun _ w' =>
      RangeOrder (wNode c.p base w') c.i w'.top.rootKey) := by
  have ht : ∀ q ∈ fromVisits (wNode c.p base w) c.i c.p.fuel (pre ++ [c0, cl]) w.top.rootKey,
      w.taken.contains q.1 = false := fun q hq =>
    hI.untaken q.1 (fromVisits_reach _ _ _ _ (fun x xn _ hn => hI.wf x xn hn) _ _ q.1 q.2
      ReachS.root hq)
  refine writerWP_mono (writerWP_put_newSeg_after c base hvc pre c0 cl h rk0 w hM hrk ht
    hI.ids.1 hI.ids.2.1 hI.ids.2.2.1 hcur) ?_
  intro _ w' ⟨L, n, hL, hn, hnl, _, htop, hL', hy', hother⟩
  rw [htop]
  have hroot : w.top.rootKey < w.next := hI.ids.2.2.2.2
  refine rangeOrder_leafAddNew (wNode c.p base w) (wNode c.p base w') c.i w.top.rootKey L w.next n _ _
    c0 hR hn hnl hL' (by rw [KNode.add_leaf]; exact hnl) ?_
    (leaf_range _ c.i _ hI.tree (fun x xn hx => hI.wf x xn hx) c.p.fuel pre c0 rk0 L hrk hL)
    (hI.none_of_ge w.next (Nat.le_refl _)) (by omega) ?_ hy' (by rw [KNode.add_leaf]) ?_
    (fun z h1 h2 => hother z h1 h2)
  · intro c' z hz
    rcases KNode.add_key_liveAt_mem n c.i c0 w.next (hI.wf L n hn) (hI.times L n hn) c' z hz with
      h1 | ⟨_, h1⟩
    · exact Or.inl h1
    · exact Or.inr h1
  · intro u c' hu hl
    obtain ⟨un, hun, hc⟩ := hl
    have := hI.links u un c' w.next (tReach_reachS _ _ _ _ hu) hun hc
    omega
  · intro c' z hm
    have he : (⟨true, []⟩ : KNode).add c.i (.key cl (w.next + 2)) =
        ⟨true, newKlongs c.i [(cl, w.next + 2)]⟩ := rfl
    rw [he] at hm
    have := liveAt_newKlongs_mem true c.i c.i _ c' z hm
    simp only [List.mem_singleton, Prod.mk.injEq] at this
    rw [this.2, hother (w.next + 2) (by have := hI.lt_next L n hn; omega) (by omega)]
    exact hI.none_of_ge _ (by omega)

end SIS.Tree
