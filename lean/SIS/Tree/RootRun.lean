/-
The space root is a key node at every time of every run (bergdb 024-12, TP7,
the root clause of the kinds): through the writer by the walk of the root
(`execW_rootWalk`), into the structure by the lift of the writer's space root
(`rootAt_commit_of_lift`), at the earlier times by `rootAt_apply_some_past`
(`treeRun_rootKeyOK`).
-/
import SIS.Tree.RootWalkRun
import SIS.Tree.KindsRun
import SIS.Tree.MergeNodeCountOps
import SIS.Tree.HistoricalRead
import SIS.Tree.InvInit

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- The space root of P at time t is a key node of P. -/
def RootKeyOK (p : Params) (P : Struct BVal) (t : Time) : Prop :=
  ∃ r nd, rootAt (viewOf P) t = some r ∧ P.get? r = some nd ∧ nd.isData = false ∧
    nd.level ≤ p.keyMax

/-- The space root names a node of P, under TP4. -/
theorem rootAt_node (P : Struct BVal) (hP : PointersOK P) (t : Time) (r : NodeId)
    (h : rootAt (viewOf P) t = some r) : ∃ nd, P.get? r = some nd := by
  unfold rootAt at h
  cases hz : topAt (viewOf P) t with
  | none => rw [hz] at h; cases h
  | some z =>
    rw [hz] at h
    simp only [Option.bind_some, rootKeyOf, viewOf] at h
    cases hg : P.get? z with
    | none => rw [hg] at h; cases h
    | some nz =>
      rw [hg] at h
      simp only [Option.bind_some] at h
      obtain ⟨e, he, hev⟩ := List.exists_of_findSome?_eq_some h
      have hval : e.val = .rootKey r := by
        revert hev
        cases e.val <;> simp
      have hs := hP _ (mem_of_get? hg) e he r (by rw [hval]; simp [bptrs])
      cases hr : P.get? r with
      | none => rw [hr] at hs; cases hs
      | some nd => exact ⟨nd, rfl⟩

/-- The space root at every time of every run within reach is a key node,
from TP4 for every run. -/
theorem treeRun_rootKeyOK (p : Params) (hM : 2 ≤ p.M)
    (hP : ∀ ts, Within p ts → PointersOK (treeRun p ts)) (ts : List Tx) (hw : Within p ts) :
    ∀ t ≤ ts.length, RootKeyOK p (treeRun p ts) t := by
  have hN : ∀ ts, Within p ts → KeyNonempty p (treeRun p ts) :=
    fun ts hw => (runLinksOK_of_pointers p (by omega) hP ts hw).2.2
  have hlift := commitLiftOK_of_overlay p (overlayLiftOK_of_links p hP hN)
  have hk : ∀ n, n ≤ ts.length → ∀ t ≤ n, RootKeyOK p (treeRun p (ts.take n)) t := by
    intro n
    induction n with
    | zero =>
      intro _ t ht
      have ht0 : t = 0 := by omega
      subst ht0
      have h0 : treeRun p (ts.take 0) = initStruct p := by simp [treeRun]
      rw [h0]
      refine ⟨1, _, rootAt_init p 0, rfl, rfl, ?_⟩
      show 1 + (p.G - 0) * (p.H + 1) + 0 ≤ 1 + p.G * (p.H + 1) + p.H
      rw [Nat.sub_zero, Nat.add_zero]
      exact Nat.le_add_right _ _
    | succ n ih =>
      intro hn t ht
      have hlt : n < ts.length := by omega
      have htake : ts.take (n + 1) = ts.take n ++ [ts[n]] := List.take_succ_eq_append_getElem hlt
      have hwn : Within p (ts.take n ++ [ts[n]]) := by
        rw [← htake]; exact within_take p ts hw (n + 1)
      have hwts := within_take p ts hw n
      have hPn := hP (ts.take n) hwts
      obtain ⟨hP', hH, hN'⟩ := runLinksOK_of_pointers p (by omega) hP (ts.take n) hwts
      obtain ⟨bs, w, he0⟩ := execW_success_of_within_snoc p (ts.take n) ts[n] hwn
      have hlen : (ts.take n).length = n := by simp; omega
      have hfresh := (hw.2 n hlt).1
      have htimes : StructTimesLE (treeRun p (ts.take n)) ((ts.take n).length + 1 - 1) :=
        treeRun_timesLE p (ts.take n)
      have htimes' : StructTimesLE (treeRun p (ts.take n)) (ts.take n).length :=
        treeRun_timesLE p (ts.take n)
      have hl := viewLinksOK_of p _ _ ts[n].base hfresh htimes hP' hN'
      have hrun : runOps p ts[n].base ts[n].ops ((ts.take n).length + 1)
          (view (treeSpec p) (treeRun p (ts.take n)) (ts.take n).length) = .ok (bs, w) := he0
      have he : execW p ts[n] ((ts.take n).length + 1)
          (view (treeSpec p) (treeRun p (ts.take n)) ((ts.take n).length + 1 - 1)) =
            .ok (bs, w) := hrun
      have he' : execW p ts[n] ((ts.take n).length + 1)
          (view (treeSpec p) (treeRun p (ts.take n)) (ts.take n).length) = .ok (bs, w) := hrun
      have hbook := execW_book p ts[n] ((ts.take n).length + 1) _ bs w
        (viewIdsBelow_view p (treeRun p (ts.take n)) ((ts.take n).length + 1 - 1) ts[n].base
          hfresh) he
      rw [htake]
      rcases Nat.lt_or_ge t (n + 1) with htl | htg
      · obtain ⟨r, nd, hr, hnd, hd, hlv⟩ := ih (by omega) t (by omega)
        rw [treeRun_snoc_changes p (ts.take n) ts[n] bs w hrun]
        exact ⟨r, _, rootAt_apply_some_past _ _ t _ (by omega) r hr, get?_apply_of_get? hnd, hd, hlv⟩
      · have htn : t = (ts.take n).length + 1 := by omega
        subst htn
        obtain ⟨hK, htk, htop⟩ := hlift (ts.take n) ts[n] hwn bs w hrun
        have hroot := rootAt_commit_of_lift p (ts.take n) ts[n] hwn bs w hrun hK htk htop
        have hKA := treeRun_kindsAllOK p hM hP (ts.take n) hwts
        have hRK := execW_rootWalk (kindOracleOf p (treeRun p (ts.take n))) p ts[n]
          ((ts.take n).length + 1) _ bs w hM (hw.1 ts[n] (List.getElem_mem hlt)).2
          (appendFrameOK ts[n].base)
          (viewIdsBelow_view p (treeRun p (ts.take n)) (ts.take n).length ts[n].base hfresh)
          (viewKinds_of p (treeRun p (ts.take n)) (ts.take n).length ts[n].base hfresh htimes' hPn hKA)
          (by
            intro z top hz htopz
            have hr0 := rootAt_of_writerTop p (ts.take n) z top hz htopz
            obtain ⟨r, nd, hr, hnd, hd, hlv⟩ := ih (by omega) (ts.take n).length (by omega)
            rw [hr0] at hr
            simp only [Option.some.injEq] at hr
            subst hr
            exact ⟨_, nd, hnd, hd, hlv, rfl⟩) he'
        have hP2 := hP _ hwn
        obtain ⟨ny, hy⟩ := rootAt_node _ hP2 _ _ hroot
        refine ⟨w.top.rootKey, ny, hroot, hy, ?_⟩
        rw [treeRun_snoc_changes p (ts.take n) ts[n] bs w hrun] at hy
        obtain ⟨g, hg⟩ := hRK
        have := kindsStep_keySeg p (treeRun p (ts.take n)) ((ts.take n).length + 1) ts[n] bs w
          hfresh htimes he hbook _ g hg ny hy
        exact ⟨this.1, this.2.1⟩
  have h := hk ts.length (Nat.le_refl _)
  rwa [List.take_length] at h

end SIS.Tree
