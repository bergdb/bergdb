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

/-- `innerChildren_of_kinds` at a state that a prefix of a transaction's
operations reaches, in a run within reach, from TP4 for every run: the books
and the kinds of the overlay there by the walk (`kd_ops`), the kinds of the
structure by `treeRun_kindsAllOK`. -/
theorem innerChildren_reached (p : Params) (hM : 2 ≤ p.M)
    (hP : ∀ ts, Within p ts → PointersOK (treeRun p ts))
    (ts : List Tx) (tx : Tx) (hw : Within p (ts ++ [tx])) (top : Top)
    (pre post : List Op) (hsplit : tx.ops = pre ++ post) (r : List Bool) (w : W)
    (h : (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w))
    (hun : ∀ x, TReach (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey x →
      w.taken.contains x = false) :
    ∀ y yn cc z, TReach (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey y →
      wNode p (viewOf (treeRun p ts)) w y = some yn → yn.leaf = false →
      (cc, z) ∈ yn.liveAt (ts.length + 1) →
      ∃ m, wNode p (viewOf (treeRun p ts)) w z = some m := by
  have hwts : Within p ts := by
    have := within_take p (ts ++ [tx]) hw ts.length
    simpa using this
  have hfresh : ∀ q ∈ treeRun p ts, q.1 < tx.base := by
    have := (hw.2 ts.length (by simp)).1
    simpa using this
  have hwf : tx.wf = true := (hw.1 tx (by simp)).2
  have hkeys : ∀ op ∈ pre, keyWf op.key = true := by
    intro op hop
    unfold Tx.wf at hwf
    exact List.all_eq_true.mp hwf op (by rw [hsplit]; exact List.mem_append_left _ hop)
  have hK := treeRun_kindsAllOK p hM hP ts hwts
  have hkd := kd_ops (kindOracleOf p (treeRun p ts)) tx.base (appendFrameOK tx.base) pre
    (ctxOf p ts) (wInit tx top)
    (viewIdsBelow_rootless _ _ (viewIdsBelow_view p (treeRun p ts) ts.length tx.base hfresh))
    (viewKinds_of p (treeRun p ts) ts.length tx.base hfresh (treeRun_timesLE p ts) (hP ts hwts) hK)
    (book_start _ _ top) (kdInv_start _ _ top) hM hkeys r w h
  exact innerChildren_of_kinds p (treeRun p ts) tx.base (ctxOf p ts) w rfl hK (hP ts hwts) hkd.1
    hkd.2.1.cache hun

end SIS.Tree
