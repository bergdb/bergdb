/-
The kinds of the nodes after every run (bergdb 024-12, TP7): the walk of the
kinds through the writer (`execW_kinds`) and the step of a run
(`kindsAllOK_step`), by induction over the run's transactions
(`treeRun_kindsAllOK`), as `treeRun_leftAllOK`.
-/
import SIS.Tree.LeftRun
import SIS.Tree.KindsStep
import SIS.Tree.WriterKindsRun
import SIS.Tree.WriterFrame

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- Every klong of every key node names a node of the right kind, after every
run within reach, from TP4. -/
theorem treeRun_kindsAllOK (p : Params) (hM : 2 ≤ p.M)
    (hP : ∀ ts, Within p ts → PointersOK (treeRun p ts)) (ts : List Tx) (hw : Within p ts) :
    KindsAllOK p (treeRun p ts) := by
  have hk : ∀ n, n ≤ ts.length → KindsAllOK p (treeRun p (ts.take n)) := by
    intro n
    induction n with
    | zero =>
      intro _
      have h0 : treeRun p (ts.take 0) = initStruct p := by simp [treeRun]
      rw [h0]
      exact kindsAllOK_init p
    | succ n ih =>
      intro hn
      have hlt : n < ts.length := by omega
      have htake : ts.take (n + 1) = ts.take n ++ [ts[n]] := List.take_succ_eq_append_getElem hlt
      have hwn : Within p (ts.take n ++ [ts[n]]) := by
        rw [← htake]; exact within_take p ts hw (n + 1)
      have hPn := hP (ts.take n) (within_take p ts hw n)
      obtain ⟨hP', hH, hN⟩ := runLinksOK_of_pointers p (by omega) hP (ts.take n)
        (within_take p ts hw n)
      obtain ⟨bs, w, he0⟩ := execW_success_of_within_snoc p (ts.take n) ts[n] hwn
      have hfresh := (hw.2 n hlt).1
      have htimes : StructTimesLE (treeRun p (ts.take n)) ((ts.take n).length + 1 - 1) :=
        treeRun_timesLE p (ts.take n)
      have htimes' : StructTimesLE (treeRun p (ts.take n)) (ts.take n).length :=
        treeRun_timesLE p (ts.take n)
      have hl := viewLinksOK_of p _ _ ts[n].base hfresh htimes hP' hN
      have hrun : runOps p ts[n].base ts[n].ops ((ts.take n).length + 1)
          (view (treeSpec p) (treeRun p (ts.take n)) (ts.take n).length) = .ok (bs, w) := he0
      have he : execW p ts[n] ((ts.take n).length + 1)
          (view (treeSpec p) (treeRun p (ts.take n)) ((ts.take n).length + 1 - 1)) =
            .ok (bs, w) := hrun
      have he' : execW p ts[n] ((ts.take n).length + 1)
          (view (treeSpec p) (treeRun p (ts.take n)) (ts.take n).length) = .ok (bs, w) := hrun
      have hvg := viewGood_of p (treeRun p (ts.take n)) ((ts.take n).length + 1) ts[n].base
        (by omega) hfresh htimes hl
      have hbook := execW_book p ts[n] ((ts.take n).length + 1) _ bs w
        (viewIdsBelow_view p (treeRun p (ts.take n)) ((ts.take n).length + 1 - 1) ts[n].base
          hfresh) he
      have htaken := execW_takenAbove p ts[n] ((ts.take n).length + 1) _ bs w hvg he
      have hKW := execW_kinds (kindOracleOf p (treeRun p (ts.take n))) p ts[n]
        ((ts.take n).length + 1) _ bs w hM (hw.1 ts[n] (List.getElem_mem hlt)).2
        (appendFrameOK ts[n].base)
        (viewIdsBelow_view p (treeRun p (ts.take n)) (ts.take n).length ts[n].base hfresh)
        (viewKinds_of p (treeRun p (ts.take n)) (ts.take n).length ts[n].base hfresh htimes' hPn
          (ih (by omega))) he'
      rw [htake, treeRun_snoc_changes p (ts.take n) ts[n] bs w hrun]
      exact kindsAllOK_step p _ ((ts.take n).length + 1) ts[n] bs w (by omega) hfresh htimes
        (treeRun_root_level p _) hH hl hPn he hbook htaken (ih (by omega)) hKW
  have h := hk ts.length (Nat.le_refl _)
  rwa [List.take_length] at h

end SIS.Tree
