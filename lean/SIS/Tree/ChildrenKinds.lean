/-
A child of a reached inner node of the writer's tree exists (bergdb 024-12,
TP7 and TP10): the fourth part of prover cost's `CollInv`
(`InnerChildrenExist`), from the walk of the kinds (`KindCache`: an inner
overlay node's klongs name key nodes of its segment), the kinds and pointers
of the structure (`KindsAllOK`, `PointersOK`) for the nodes of the view, and
no reached node taken back.
-/
import SIS.Tree.KindsRun
import SIS.Tree.WriterTree

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- Every live child of a reached inner node of the writer's tree over the
structure P is a node: the statement of `InnerChildrenExist` for
`wNode c.p (viewOf P) w` from the root `w.top.rootKey` at `c.i`. -/
theorem innerChildren_of_kinds (p : Params) (P : Struct BVal) (B : NodeId) (c : Ctx) (w : W)
    (hcp : c.p = p) (hK : KindsAllOK p P) (hP : PointersOK P) (hb : Book B c w)
    (hcache : KindCache (kindOracleOf p P) w)
    (hun : ∀ x, TReach (wNode c.p (viewOf P) w) c.i w.top.rootKey x → w.taken.contains x = false) :
    ∀ y yn cc z, TReach (wNode c.p (viewOf P) w) c.i w.top.rootKey y →
      wNode c.p (viewOf P) w y = some yn → yn.leaf = false → (cc, z) ∈ yn.liveAt c.i →
      ∃ m, wNode c.p (viewOf P) w z = some m := by
  intro y yn cc z hy hyn hyl hlive
  have hzR : TReach (wNode c.p (viewOf P) w) c.i w.top.rootKey z := TReach.link hy ⟨yn, hyn, hlive⟩
  have hzt := hun z hzR
  have hk : Klong.key cc z ∈ yn.ks := KNode.liveAt_key_mem yn c.i cc z hlive
  -- a key node of P is a node of the writer's tree, unless the overlay has it
  have hofP : ∀ nz : Node BVal, P.get? z = some nz → nz.isData = false → nz.level ≤ p.keyMax →
      ∃ m, wNode c.p (viewOf P) w z = some m := by
    intro nz hz hd hl
    unfold wNode
    rw [hzt]
    simp only [Bool.false_eq_true, ↓reduceIte]
    cases hlz : w.nodes.lookup z with
    | some m => exact ⟨m, rfl⟩
    | none =>
      simp [knodeOf, viewOf, hz, hd, hcp, Nat.not_lt.mpr hl]
  unfold wNode at hyn
  have hyt : w.taken.contains y = false := hun y hy
  rw [hyt] at hyn
  simp only [Bool.false_eq_true, ↓reduceIte] at hyn
  cases hly : w.nodes.lookup y with
  | some n =>
    rw [hly] at hyn
    simp only [Option.some.injEq] at hyn
    subst hyn
    obtain ⟨g, h, hgh⟩ := kd_tag_of_lookup hb hly
    have hleaf := kd_leaf hb hly hgh
    have hh : h ≠ 0 := by
      intro h0; rw [h0] at hleaf; rw [hleaf] at hyl; simp at hyl
    have hkk := (hcache y n g h (bk_mem_of_lookup _ _ _ hly) hgh cc z hk).1 hh
    rcases hkk with ⟨h', hm'⟩ | ⟨nz, hz, hd, hl, _⟩
    · obtain ⟨m, hm⟩ := kd_lookup_of_tag hb hm'
      refine ⟨m, ?_⟩
      unfold wNode
      rw [hzt]
      simp only [Bool.false_eq_true, ↓reduceIte, hm]
    · exact hofP nz hz hd hl
  | none =>
    rw [hly] at hyn
    simp only [knodeOf, viewOf] at hyn
    cases hpy : P.get? y with
    | none => rw [hpy] at hyn; cases hyn
    | some nd =>
      rw [hpy] at hyn
      simp only at hyn
      split at hyn
      · cases hyn
      · rename_i hcond
        simp only [Option.some.injEq] at hyn
        subst hyn
        simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, Bool.not_eq_true] at hcond
        obtain ⟨hd, hlv⟩ := hcond
        rw [hcp] at hlv hyl
        have hlv' : nd.level ≤ p.keyMax := by omega
        have hh : p.heightOf nd.level ≠ 0 := by
          intro h0; simp [h0] at hyl
        obtain ⟨nz, hz⟩ := kindsStep_ptr P hP y nd hpy cc z hk
        obtain ⟨hzd, hzl, _⟩ := (hK y nd hpy hd hlv' cc z hk nz hz).1 hh
        exact hofP nz hz hzd hzl

end SIS.Tree
