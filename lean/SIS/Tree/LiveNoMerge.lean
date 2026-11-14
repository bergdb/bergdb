/-
With TP7's live counts, the merges' loop merges nothing (bergdb 024-12, a piece
for `QLive` of (4)): every node that an inner node names holds at least
`mergeBelow` live klongs (`LiveCounts`), so the loop's test `cnt < mergeBelow`
under an inner parent never holds, and `afterDelete` reads as before
(`writerWP_mergeUp_none`, `writerWP_afterDelete_none`). A delete whose bitmap
leaves the live counts as they were, the merges on, so changes only its leaf.
-/
import SIS.Tree.LiveJointL
import SIS.Tree.StopLeafLive
import SIS.Tree.GetDescentOK
import SIS.Tree.MergePathCache

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- The merges' loop at a state with the live counts, the merges on: it merges
nothing, returns its flag and reads as before. -/
theorem writerWP_mergeUp_none (key : Key) (g : Nat) (c : Ctx) (base : View BVal)
    (hvc : ViewCoherent c base) (hm : c.p.merges = true) (fuel h : Nat) (merged : Bool) (v : W)
    (hRt : ∀ y, TReach (wNode c.p base v) c.i v.top.rootKey y → v.taken.contains y = false)
    (hwf : ∀ y yn, TReach (wNode c.p base v) c.i v.top.rootKey y → wNode c.p base v y = some yn →
      klongsWf yn.ks = true)
    (htimes : ∀ y yn, wNode c.p base v y = some yn → ∀ s, Klong.time s ∈ yn.ks → s ≤ c.i)
    (hLC : LiveCounts c.p (wNode c.p base v) c.i v.top.rootKey) :
    WriterWP (mergeUp key g fuel h merged) c v (fun r v' => r = merged ∧ ReadsAs c.p base v v') := by
  cases fuel with
  | zero => rw [mergeUp]; exact writerWP_throw _ _ _ _
  | succ f =>
    rw [mergeUp]
    simp only [writerWP_bind, writerWP_read]
    refine writerWP_mono (writerWP_and (writerWP_descendToHeight_linked key g h c base hvc v hRt hwf)
      (writerWP_descendToHeight_path_cached key g h c v)) ?_
    rintro d v1 ⟨⟨hr1, ps, hp1, hlf, hd⟩, hpc⟩
    by_cases hd0 : d = 0
    · simp only [hd0, BEq.rfl, ↓reduceIte, writerWP_pure]
      exact ⟨by simp, hr1⟩
    · have hbeq : (d == 0) = false := by simp [hd0]
      simp only [hbeq, Bool.false_eq_true, ↓reduceIte]
      obtain ⟨hX, _, hN, hL, hX0⟩ := pathOK_of_linked c base v v1 ps hr1 hp1 hlf hpc hRt
      try dsimp only at hX
      try dsimp only at hN
      try dsimp only at hL
      try dsimp only at hX0
      subst hd
      have hXd := hX ps.length (Nat.le_refl _)
      have hXq := hX (ps.length - 1) (by omega)
      obtain ⟨hNd, hTd⟩ := hN ps.length (Nat.le_refl _)
      obtain ⟨hNq, hTq⟩ := hN (ps.length - 1) (by omega)
      cases he : v1.path[ps.length]? with
      | none => rw [he] at hXd; cases hXd
      | some e =>
        cases hq : v1.path[ps.length - 1]? with
        | none => rw [hq] at hXq; cases hXq
        | some q =>
          rw [he] at hXd
          rw [hq] at hXq
          simp only [Option.map_some, Option.some.injEq] at hXd hXq
          simp only [pathNode, he, hq, writerWP_bind, writerWP_pure, writerWP_get]
          rw [hXq, writerWP_getNode_known _ _ c v1 hNq]
          split
          · simp only [writerWP_pure]
            exact ⟨by simp, hr1⟩
          · rename_i hleaf0
            have hleaf : ((wNode c.p base v (nodeAt v.top.rootKey ps (ps.length - 1))).getD
                ⟨true, []⟩).leaf = false := by simpa using hleaf0
            simp only [writerWP_bind]
            rw [hXd, writerWP_getNode_known _ _ c v1 hNd]
            -- the node below an inner node of the path holds at least mergeBelow live klongs
            have hwN : ∀ i, i ≤ ps.length → wNode c.p base v (nodeAt v.top.rootKey ps i) =
                some ((wNode c.p base v (nodeAt v.top.rootKey ps i)).getD ⟨true, []⟩) := by
              intro i hi
              obtain ⟨hNi, hTi⟩ := hN i hi
              have : wNode c.p base v1 (nodeAt v.top.rootKey ps i) =
                  some ((wNode c.p base v (nodeAt v.top.rootKey ps i)).getD ⟨true, []⟩) := by
                simp only [wNode, hTi, Bool.false_eq_true, ↓reduceIte, hNi]
              exact (congrFun hr1.1 _).symm.trans this
            obtain ⟨b, s, hfr⟩ := fReach_path (wNode c.p base v) c.i v.top.rootKey
              (fun i => nodeAt v.top.rootKey ps i)
              (fun i => (wNode c.p base v (nodeAt v.top.rootKey ps i)).getD ⟨true, []⟩)
              (fun i => ((ps[i - 1]?).bind (·.1)).getD 0) ps.length (hX0.trans (by rw [hr1.2.1])) hwN hL (ps.length - 1) (by omega)
            have hl := hL ps.length (by omega) (Nat.le_refl _)
            have hfr2 := FReach.inner _ b s _ _ _ hfr (hwN (ps.length - 1) (by omega)) hleaf hl
            have hcnt := (hLC _ false s _ hfr2 (hwN ps.length (Nat.le_refl _))).2.2 hm rfl
            rw [KNode.liveAt_of_times _ _ (htimes _ _ (hwN ps.length (Nat.le_refl _)))] at hcnt
            have hge : c.p.mergeBelow ≤
                ((wNode c.p base v (nodeAt v.top.rootKey ps ps.length)).getD ⟨true, []⟩).cnt := hcnt
            split
            · simp only [writerWP_pure]
              exact ⟨by simp, hr1⟩
            · rename_i hlt
              exact absurd hge hlt

/-- `afterDelete` at a state with the live counts, the merges on: it merges
nothing and reads as before. -/
theorem writerWP_afterDelete_none (key : Key) (g h : Nat) (c : Ctx) (base : View BVal)
    (hvc : ViewCoherent c base) (v : W)
    (hRt : ∀ y, TReach (wNode c.p base v) c.i v.top.rootKey y → v.taken.contains y = false)
    (hwf : ∀ y yn, TReach (wNode c.p base v) c.i v.top.rootKey y → wNode c.p base v y = some yn →
      klongsWf yn.ks = true)
    (htimes : ∀ y yn, wNode c.p base v y = some yn → ∀ s, Klong.time s ∈ yn.ks → s ≤ c.i)
    (hLC : LiveCounts c.p (wNode c.p base v) c.i v.top.rootKey) :
    WriterWP (afterDelete key g h) c v (fun _ v' => ReadsAs c.p base v v') := by
  unfold afterDelete
  simp only [writerWP_bind, writerWP_read]
  split
  · rename_i hm
    rw [writerWP_bind]
    refine writerWP_mono (writerWP_mergeUp_none key g c base hvc hm c.p.fuel h false v hRt hwf htimes hLC) ?_
    rintro r v1 ⟨hr, hr1⟩
    subst hr
    simp only [Bool.false_eq_true, ↓reduceIte, writerWP_pure]
    exact hr1
  · simp only [writerWP_pure]
    exact ReadsAs.refl _ _ _

end SIS.Tree
