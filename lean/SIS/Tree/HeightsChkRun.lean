/-
TP7's (b), the live heights after every run, from one named premise
(bergdb 024-22, step 4): `OpDelChkOK`, a delete, from a state that the
transaction's earlier operations reach, runs as its copy with the checks
(`putKvDelChk`, SIS/Tree/DelChk.lean). The checks are those of the take-backs'
holders, the parent of the upward delete's take-back a segment leaf, and its
stop node a segment leaf with the path above it not taken back. With the
premise the walk of the heights needs no other (`opHtDelOK_of_chk`). The premise
is checked on runs by a check outside the repository (DelChk.lean, 2026-11-13).
-/
import SIS.Tree.HeightsRun
import SIS.Tree.WriterHeightsChkDel

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- The delete's checks hold (named premise): a delete, from a state that the
transaction's earlier operations reach, runs as its copy with the checks. -/
def OpDelChkOK (p : Params) : Prop :=
  ∀ ts tx, Within p (ts ++ [tx]) → ∀ z top,
    lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z →
    topOf p (ctxOf p ts).view z = .ok top →
    ∀ pre key post, tx.ops = pre ++ Op.del key :: post →
    ∀ r w, (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
    ∀ r' v, putKv (.del key) (ctxOf p ts) w = .ok (r', v) →
      putKvDelChk key (ctxOf p ts) w = .ok (r', v)

/-- The delete side of the walk from the delete's checks. -/
theorem opHtDelOK_of_chk (p : Params) (h : OpDelChkOK p) : OpHtDelOK p := by
  intro ts tx hw z top hz htop pre key post hsplit r w hpre hvo hkw hb hwf hi r' v he
  exact (ht_putKvDelChk tx.base key (ctxOf p ts) w hvo (by simp [ctxOf]) hkw hb hi hwf r' v
    (h ts tx hw z top hz htop pre key post hsplit r w hpre r' v he)).2.1

end SIS.Tree
