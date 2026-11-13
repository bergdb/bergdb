/-
A merge below a parent without room keeps the take-back's (B), (C) and node
facts (bergdb 024-12, TP7, case (4)'s `MergeFullJ2OKF`): the node-map step
(`j2rest_mergeFull`): the parent's cascade (latest's shapes, `CascadeShapeJ2`),
the merged nodes made at t, and the two nodes merged taken back or unlinked.
-/
import SIS.Tree.TakeDeadLast
import SIS.Tree.TakeDeadMerge
import SIS.Tree.LevelShape
import SIS.Tree.MergeLastOrd

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- A node merged away, unlinked: its (C) and node facts, for an old node. -/
theorem unlinked_j2 (N : NodeId → Option KNode) (t : Time) (B : NodeId) (vals : List NodeId)
    (hpos : 0 < t) (hD : DeadLiveN N t B vals) (hO : OldBelowN N t B) (hS : OldStartN N t B)
    (x : NodeId) (xn : KNode) (hx : N x = some xn) (hxB : x < B) :
    DeadLiveK (unlinkedNode xn t) t B vals ∧
    (∀ cv y, Klong.key cv y ∈ prefixAt (unlinkedNode xn t).ks (t - 1) → y < B) ∧
    (∃ s, s < t ∧ (unlinkedNode xn t).firstTime = some s) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i cv y hi hB hv
    unfold unlinkedNode at hi ⊢
    split at hi
    · have hm : Klong.key cv y ∈ prefixAt xn.ks (t - 1) := List.mem_of_getElem? hi
      have := hO x xn hx cv y hm
      omega
    · rename_i hne
      simp only [hne, Bool.false_eq_true, ↓reduceIte]
      exact hD x xn hx i cv y hi hB hv
  · intro cv y hk
    rw [(unlinked_facts xn t hpos).1] at hk
    exact hO x xn hx cv y hk
  · obtain ⟨s, hs, hf⟩ := hS x xn hx hxB
    exact ⟨s, hs, (unlinked_facts xn t hpos).2 s hs hf⟩

/-- (C) and the node facts after a merge below a full parent: the cascade along
X s .. X D (the parent its last) with `CascadeShapeJ2` for its changed and made
nodes (the merged nodes among them), the two nodes merged, l and r, taken back
or unlinked (old ones), and every other node below nx as before. -/
theorem j2rest_mergeFull (N N' : NodeId → Option KNode) (t : Time) (r0 B : NodeId)
    (vals : List NodeId) (X : Nat → NodeId) (Nn : Nat → KNode) (s D : Nat) (nx : NodeId)
    (hpos : 0 < t) (hT : TreeOK N t r0) (hD : DeadLiveN N t B vals) (hO : OldBelowN N t B)
    (hS : OldStartN N t B) (hM : MadeStartN N t B) (hV : ValsNoNodeN N vals)
    (hN : ∀ i, s ≤ i → i ≤ D → N (X i) = some (Nn i))
    (hwf : ∀ i, s ≤ i → i ≤ D → klongsWf (Nn i).ks = true)
    (hts : ∀ i, s ≤ i → i ≤ D → ∀ u, Klong.time u ∈ (Nn i).ks → u ≤ t)
    (hR : ∀ i, s ≤ i → i ≤ D → TReach N t r0 (X i)) (hvnx : ∀ y ∈ vals, y < nx)
    (l r : NodeId) (ln rn : KNode) (hln : N l = some ln) (hrn : N r = some rn)
    (hlX : ∀ i, s ≤ i → i ≤ D → l ≠ X i) (hrX : ∀ i, s ≤ i → i ≤ D → r ≠ X i)
    (hlnx : l < nx) (hrnx : r < nx)
    (hlF : N' l = none ∨ (N' l = some (unlinkedNode ln t) ∧ ln.firstTime ≠ some t))
    (hrF : N' r = none ∨ (N' r = some (unlinkedNode rn t) ∧ rn.firstTime ≠ some t))
    (hother : ∀ z, z < nx → (∀ i, s ≤ i → i ≤ D → z ≠ X i) → z ≠ l → z ≠ r → N' z = N z)
    (hshape : ∀ z zn, N' z = some zn → (nx ≤ z ∨ ∃ i, s ≤ i ∧ i ≤ D ∧ z = X i) →
      CascadeShapeJ2 N t B vals X Nn s D z zn) :
    DeadLiveN N' t B vals ∧ OldBelowN N' t B ∧ OldStartN N' t B ∧ MadeStartN N' t B ∧
      ValsNoNodeN N' vals := by
  let N'' : NodeId → Option KNode := fun z => if z = l ∨ z = r then N z else N' z
  have hoff : ∀ z, (z = l ∨ z = r) → ¬ (nx ≤ z ∨ ∃ i, s ≤ i ∧ i ≤ D ∧ z = X i) := by
    intro z hz h
    rcases h with h | ⟨i, a, b, rfl⟩
    · rcases hz with rfl | rfl <;> omega
    · rcases hz with h | h
      · exact hlX i a b h.symm
      · exact hrX i a b h.symm
  obtain ⟨hD'', hO'', hS'', hM'', hV''⟩ := j2rest_cascade2 N N'' t r0 B vals X Nn s D nx hpos hT hD hO hS
    hM hV hN hwf hts hR hvnx
    (fun z hz hnc => by
      by_cases hzlr : z = l ∨ z = r
      · simp only [N'', hzlr, ↓reduceIte]
      · simp only [N'', hzlr, ↓reduceIte]
        exact hother z hz hnc (fun h => hzlr (Or.inl h)) (fun h => hzlr (Or.inr h)))
    (fun z zn hzn hz => by
      by_cases hzlr : z = l ∨ z = r
      · exact absurd hz (hoff z hzlr)
      · simp only [N'', hzlr, ↓reduceIte] at hzn
        exact hshape z zn hzn hz)
  have hN'' : ∀ z, z ≠ l → z ≠ r → N' z = N'' z := by
    intro z h1 h2
    have : ¬ (z = l ∨ z = r) := fun h => h.elim h1 h2
    simp only [N'', this, ↓reduceIte]
  -- the two nodes merged
  have hmerged : ∀ (x : NodeId) (xn : KNode), N x = some xn →
      (N' x = none ∨ (N' x = some (unlinkedNode xn t) ∧ xn.firstTime ≠ some t)) →
      ∀ qn, N' x = some qn → qn = unlinkedNode xn t ∧ x < B := by
    intro x xn hx hF qn hq
    rcases hF with h | ⟨h, hft⟩
    · rw [h] at hq; cases hq
    · rw [h] at hq; cases hq
      exact ⟨rfl, lt_of_firstTime_ne N t B hM x xn hx hft⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro q qn hq
    by_cases hql : q = l
    · subst hql
      obtain ⟨he, hB'⟩ := hmerged q ln hln hlF qn hq
      subst he
      exact (unlinked_j2 N t B vals hpos hD hO hS q ln hln hB').1
    · by_cases hqr : q = r
      · subst hqr
        obtain ⟨he, hB'⟩ := hmerged q rn hrn hrF qn hq
        subst he
        exact (unlinked_j2 N t B vals hpos hD hO hS q rn hrn hB').1
      · rw [hN'' q hql hqr] at hq
        exact hD'' q qn hq
  · intro q qn hq cv y hk
    by_cases hql : q = l
    · subst hql
      obtain ⟨he, hB'⟩ := hmerged q ln hln hlF qn hq
      subst he
      exact (unlinked_j2 N t B vals hpos hD hO hS q ln hln hB').2.1 cv y hk
    · by_cases hqr : q = r
      · subst hqr
        obtain ⟨he, hB'⟩ := hmerged q rn hrn hrF qn hq
        subst he
        exact (unlinked_j2 N t B vals hpos hD hO hS q rn hrn hB').2.1 cv y hk
      · rw [hN'' q hql hqr] at hq
        exact hO'' q qn hq cv y hk
  · intro q qn hq hqB
    by_cases hql : q = l
    · subst hql
      obtain ⟨he, hB'⟩ := hmerged q ln hln hlF qn hq
      subst he
      exact (unlinked_j2 N t B vals hpos hD hO hS q ln hln hB').2.2
    · by_cases hqr : q = r
      · subst hqr
        obtain ⟨he, hB'⟩ := hmerged q rn hrn hrF qn hq
        subst he
        exact (unlinked_j2 N t B vals hpos hD hO hS q rn hrn hB').2.2
      · rw [hN'' q hql hqr] at hq
        exact hS'' q qn hq hqB
  · intro q qn hq hqB
    by_cases hql : q = l
    · subst hql
      obtain ⟨_, hB'⟩ := hmerged q ln hln hlF qn hq
      omega
    · by_cases hqr : q = r
      · subst hqr
        obtain ⟨_, hB'⟩ := hmerged q rn hrn hrF qn hq
        omega
      · rw [hN'' q hql hqr] at hq
        exact hM'' q qn hq hqB
  · intro y hy
    by_cases hyl : y = l
    · subst hyl
      have := hV y hy
      rw [hln] at this; cases this
    · by_cases hyr : y = r
      · subst hyr
        have := hV y hy
        rw [hrn] at this; cases this
      · rw [hN'' y hyl hyr]
        exact hV'' y hy

/-- A step of the merge's cleanup when the parent has no klong of the
transaction naming the node merged: the parent is kept, the node taken back or
unlinked. -/
theorem writerWP_mergeCleanup_stepF (p m1 : NodeId) (c : Ctx) (q : NodeId × Bool) (w : W)
    (pn qn : KNode) (hp : w.nodes.lookup p = some pn) (hq : w.nodes.lookup q.1 = some qn)
    (hqp : q.1 ≠ p) (hnone : pn.lastTime = some c.i → ∀ cv y, Klong.key cv y ∈ pn.ks → y ≠ q.1) :
    WriterWP ((if q.2 = true then (do
        retarget p q.1 m1
        takenBack q.1
        note "merge.takeback"
        pure (ForInStep.yield PUnit.unit)) else (do
        unlink q.1
        pure (ForInStep.yield PUnit.unit))) : M (ForInStep PUnit)) c w (fun s w' =>
      s = ForInStep.yield PUnit.unit ∧ w'.top = w.top ∧ w'.vals = w.vals ∧
      (∀ y, y ≠ q.1 → w'.taken.contains y = w.taken.contains y) ∧
      (q.2 = true → w'.taken.contains q.1 = true) ∧
      (q.2 = false → w'.taken.contains q.1 = w.taken.contains q.1) ∧
      (∀ y, y ≠ q.1 → w'.nodes.lookup y = w.nodes.lookup y) ∧
      (q.2 = false → w'.nodes.lookup q.1 = some (unlinkedNode qn c.i))) := by
  split
  · rename_i hq2
    simp only [writerWP_bind]
    unfold retarget
    simp only [writerWP_bind, writerWP_read]
    rw [writerWP_getNode_known p pn c w hp]
    split
    · rename_i hlt
      have hlt' : pn.lastTime = some c.i := by simpa using hlt
      have hid : ∀ f : Klong × Nat → Klong, (∀ q' ∈ pn.ks.zipIdx, f q' = q'.1) →
          ({ pn with ks := pn.ks.zipIdx.map f } : KNode) = pn := by
        intro f hf
        cases pn with
        | mk lf ks =>
          show KNode.mk lf _ = KNode.mk lf ks
          congr 1
          conv => rhs; rw [← (show ks.zipIdx.map Prod.fst = ks from by simp)]
          exact List.map_congr_left hf
      unfold putNode
      refine (writerWP_modify _ c w _).mpr ?_
      refine (writerWP_takenBack_iff _ c _ _).mpr ?_
      refine (writerWP_note_iff _ c _ _).mpr ?_
      refine (writerWP_pure _ c _ _).mpr ?_
      refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
      · intro y hy; simp [hy]
      · intro _; simp
      · intro h; rw [hq2] at h; cases h
      · intro y hy
        show (upsert w.nodes p _).lookup y = _
        rw [hid, lookup_upsert]
        · by_cases hyp : y = p
          · subst hyp; simp [hp]
          · simp [hyp]
        · intro q' hq'
          have hk : q'.1 ∈ pn.ks := by
            have := List.mem_map_of_mem (f := Prod.fst) hq'
            simpa using this
          rcases q' with ⟨k, i⟩
          cases k with
          | time t => rfl
          | del b => rfl
          | key cv y' =>
            have hy : (y' == q.1) = false := by simpa using hnone hlt' cv y' hk
            simp [hy]
      · intro h; rw [hq2] at h; cases h
    · simp only [writerWP_pure]
      refine (writerWP_takenBack_iff _ c _ _).mpr ?_
      refine (writerWP_note_iff _ c _ _).mpr ?_
      refine ⟨by first | rfl | trivial, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
      · intro y hy; simp [hy]
      · intro _; simp
      · intro h; rw [hq2] at h; cases h
      · intro y _; rfl
      · intro h; rw [hq2] at h; cases h
  · rename_i hq2
    simp only [writerWP_bind]
    refine writerWP_mono (writerWP_unlink_fate q.1 qn c w hq) ?_
    rintro _ w' ⟨h1, h2, h3, h4, h5⟩
    refine (writerWP_pure _ c _ _).mpr ?_
    refine ⟨rfl, h2, h3, fun y _ => by rw [h1], fun h => absurd h hq2, fun _ => by rw [h1], h5, fun _ => h4⟩

/-- The merge's cleanup when the parent has no klong of the transaction naming
either node merged: the parent and every other node kept, each node merged taken
back (made) or unlinked. -/
theorem writerWP_mergeCleanup_F (p m1 : NodeId) (c : Ctx) (l r : NodeId) (bl br : Bool)
    (pn ln rn : KNode) (w : W) (hlr : l ≠ r) (hlp : l ≠ p) (hrp : r ≠ p)
    (hp : w.nodes.lookup p = some pn) (hl : w.nodes.lookup l = some ln)
    (hr : w.nodes.lookup r = some rn)
    (hnone : pn.lastTime = some c.i → ∀ cv y, Klong.key cv y ∈ pn.ks → y ≠ l ∧ y ≠ r) :
    WriterWP (forIn [(l, bl), (r, br)] PUnit.unit (fun q _ => if q.2 = true then (do
        retarget p q.1 m1
        takenBack q.1
        note "merge.takeback"
        pure (ForInStep.yield PUnit.unit)) else (do
        unlink q.1
        pure (ForInStep.yield PUnit.unit)))) c w (fun _ w' =>
      w'.top = w.top ∧ w'.vals = w.vals ∧
      (∀ y, y ≠ l → y ≠ r → w'.taken.contains y = w.taken.contains y) ∧
      (bl = true → w'.taken.contains l = true) ∧ (br = true → w'.taken.contains r = true) ∧
      (bl = false → w'.taken.contains l = w.taken.contains l) ∧
      (br = false → w'.taken.contains r = w.taken.contains r) ∧
      (∀ y, y ≠ l → y ≠ r → w'.nodes.lookup y = w.nodes.lookup y) ∧
      (bl = false → w'.nodes.lookup l = some (unlinkedNode ln c.i)) ∧
      (br = false → w'.nodes.lookup r = some (unlinkedNode rn c.i))) := by
  rw [List.forIn_cons, writerWP_bind]
  refine writerWP_mono (writerWP_mergeCleanup_stepF p m1 c (l, bl) w pn ln hp hl hlp
    (fun h cv y hk => (hnone h cv y hk).1)) ?_
  rintro s w1 ⟨hs, h1top, h1v, h1t, h1tl, h1tk, h1n, h1ul⟩
  subst hs
  simp only
  have h1p : w1.nodes.lookup p = some pn := by rw [h1n p (Ne.symm hlp)]; exact hp
  rw [List.forIn_cons, writerWP_bind]
  refine writerWP_mono (writerWP_mergeCleanup_stepF p m1 c (r, br) w1 pn rn h1p
    (by rw [h1n r (Ne.symm hlr)]; exact hr) hrp (fun h cv y hk => (hnone h cv y hk).2)) ?_
  rintro s w2 ⟨hs, h2top, h2v, h2t, h2tr, h2tk, h2n, h2ur⟩
  subst hs
  simp only [List.forIn_nil, writerWP_pure]
  refine ⟨h2top.trans h1top, h2v.trans h1v, fun y hyl hyr => by rw [h2t y hyr, h1t y hyl], fun h => ?_, h2tr,
    fun h => ?_, fun h => by rw [h2tk h, h1t r (Ne.symm hlr)], fun y hyl hyr => by rw [h2n y hyr, h1n y hyl],
    fun h => ?_, h2ur⟩
  · rw [h2t l hlr]; exact h1tl h
  · rw [h2t l hlr]; exact h1tk h
  · rw [h2n l hlr]; exact h1ul h

/-- What a tree reaches before a merge is reached in the tree with the parent's
new content, but the two nodes merged: their children hang below the merged
nodes, the parent's other children below it. -/
theorem reach_merge_fwd (N V : NodeId → Option KNode) (t : Time) (root p l r : NodeId)
    (pn ln rn pv : KNode) (hpn : N p = some pn) (hln : N l = some ln) (hrn : N r = some rn)
    (hVp : V p = some pv)
    (hpkeep : ∀ c z, (c, z) ∈ pn.liveAt t → z ≠ l → z ≠ r → ∃ c', (c', z) ∈ pv.liveAt t)
    (hm : ∀ z, ((∃ c, (c, z) ∈ ln.liveAt t) ∨ (∃ c, (c, z) ∈ rn.liveAt t)) →
      ∃ m mn c', TReach V t root m ∧ V m = some mn ∧ (c', z) ∈ mn.liveAt t)
    (hVN : ∀ u un, u ≠ p → N u = some un → V u = some un) :
    ∀ z, TReach N t root z → z = l ∨ z = r ∨ TReach V t root z := by
  intro z hz
  induction hz with
  | root => exact Or.inr (Or.inr TReach.root)
  | @link u c z _ hl ih =>
    obtain ⟨un, hun, hc⟩ := hl
    rcases ih with hu | hu | hu
    · subst hu
      rw [hln] at hun; cases hun
      obtain ⟨m, mn, c', hmR, hmn, hc'⟩ := hm z (Or.inl ⟨c, hc⟩)
      exact Or.inr (Or.inr (TReach.link hmR ⟨mn, hmn, hc'⟩))
    · subst hu
      rw [hrn] at hun; cases hun
      obtain ⟨m, mn, c', hmR, hmn, hc'⟩ := hm z (Or.inr ⟨c, hc⟩)
      exact Or.inr (Or.inr (TReach.link hmR ⟨mn, hmn, hc'⟩))
    · by_cases hup : u = p
      · subst hup
        rw [hpn] at hun; cases hun
        by_cases hzl : z = l
        · exact Or.inl hzl
        · by_cases hzr : z = r
          · exact Or.inr (Or.inl hzr)
          · obtain ⟨c', hc'⟩ := hpkeep c z hc hzl hzr
            exact Or.inr (Or.inr (TReach.link hu ⟨pv, hVp, hc'⟩))
      · exact Or.inr (Or.inr (TReach.link hu ⟨un, hVN u un hup hun, hc⟩))

end SIS.Tree
