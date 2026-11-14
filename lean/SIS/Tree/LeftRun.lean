/-
The tree model (bergdb 024-12, TP2 and TP7): the leftmost rule after every
run within reach, from TP4. Every inner key node of the structure has a
klong and the empty key live (`treeRun_leftAllOK`): the writer keeps it
(`execW_leftOK`, SIS/Tree/WriterLeft*.lean) and the structure after a
transaction is the overlay (`leftAllOK_step`). So at a run's last time the
smallest live klong of every reachable inner node is the empty key's
(`leftmostOK_latest`, TP2 at the latest time): one part of the walk of
`LatestInvOK`.
-/
import SIS.Tree.LeftStep
import SIS.Tree.WriterLeftRun
import SIS.Tree.PointersRun

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- Every inner key node has the empty key live, after every run within
reach, under valid parameters, from TP4. -/
theorem treeRun_leftAllOK (p : Params) (hp : MergeParamsOK p)
    (hP : ∀ ts, Within p ts → PointersOK (treeRun p ts)) (ts : List Tx) (hw : Within p ts) :
    LeftAllOK p (treeRun p ts) := by
  have hM := mergeParamsOK_M p hp
  have hk : ∀ n, n ≤ ts.length → LeftAllOK p (treeRun p (ts.take n)) := by
    intro n
    induction n with
    | zero =>
      intro _
      have h0 : treeRun p (ts.take 0) = initStruct p := by simp [treeRun]
      rw [h0]
      exact leftAllOK_init p
    | succ n ih =>
      intro hn
      have hlt : n < ts.length := by omega
      have htake : ts.take (n + 1) = ts.take n ++ [ts[n]] := List.take_succ_eq_append_getElem hlt
      have hwn : Within p (ts.take n ++ [ts[n]]) := by
        rw [← htake]; exact within_take p ts hw (n + 1)
      obtain ⟨hP', hH, hN⟩ := runLinksOK_of_pointers p (by omega) hP (ts.take n)
        (within_take p ts hw n)
      obtain ⟨bs, w, he0⟩ := execW_success_of_within_snoc p (ts.take n) ts[n] hwn
      have hfresh := (hw.2 n hlt).1
      have htimes : StructTimesLE (treeRun p (ts.take n)) ((ts.take n).length + 1 - 1) :=
        treeRun_timesLE p (ts.take n)
      have hl := viewLinksOK_of p _ _ ts[n].base hfresh htimes hP' hN
      have hrun : runOps p ts[n].base ts[n].ops ((ts.take n).length + 1)
          (view (treeSpec p) (treeRun p (ts.take n)) (ts.take n).length) = .ok (bs, w) := he0
      have he : execW p ts[n] ((ts.take n).length + 1)
          (view (treeSpec p) (treeRun p (ts.take n)) ((ts.take n).length + 1 - 1)) =
            .ok (bs, w) := hrun
      have hvg := viewGood_of p (treeRun p (ts.take n)) ((ts.take n).length + 1) ts[n].base
        (by omega) hfresh htimes hl
      have hbook := execW_book p ts[n] ((ts.take n).length + 1) _ bs w
        (viewIdsBelow_view p (treeRun p (ts.take n)) ((ts.take n).length + 1 - 1) ts[n].base
          hfresh) he
      have htaken := execW_takenAbove p ts[n] ((ts.take n).length + 1) _ bs w hvg he
      have hLW := execW_leftOK p ts[n] ((ts.take n).length + 1) _ bs w hp hvg
        (viewLeftOK_of_leftAll p _ _ htimes (ih (by omega))) he
      rw [htake, treeRun_snoc_changes p (ts.take n) ts[n] bs w hrun]
      exact leftAllOK_step p _ ((ts.take n).length + 1) ts[n] bs w (by omega) hfresh htimes
        (treeRun_root_level p _) hH hl he hbook htaken (ih (by omega)) hLW
  have h := hk ts.length (Nat.le_refl _)
  rwa [List.take_length] at h

/-- TP2 at a run's last time, under valid parameters, from TP4. -/
theorem leftmostOK_latest (p : Params) (hp : MergeParamsOK p)
    (hP : ∀ ts, Within p ts → PointersOK (treeRun p ts)) (ts : List Tx) (hw : Within p ts) :
    LeftmostOK p (treeRun p ts) ts.length :=
  leftmostOK_of_leftAll p _ _ (treeRun_timesLE p ts)
    (runLinksOK_of_pointers p (by have := mergeParamsOK_M p hp; omega) hP ts hw).2.1
    (treeRun_leftAllOK p hp hP ts hw)

end SIS.Tree
