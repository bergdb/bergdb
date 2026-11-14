/-
Step 4 (B) at the operation level (bergdb 024-22; 024-12's (4)): every
operation of a transaction within reach adds at most one to the cached heights
(`opHtStep_of`). The put is proved (`seenHeight_putKv_put`); the delete is a
named premise, `OpDelHtStepOK`, checked on runs (the same bound per segment,
`/Users/f/fl/bench/2026-11-13/cost/fit/HeightsOp.lean`). A delete's bitmap, a
merge and a cascade each add at most one (proved); a whole delete runs several
merges, and one per operation needs the merges' fill.
-/
import SIS.Tree.HeightsFit
import SIS.Tree.HeightsFuelPut

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- A delete, from a state that the transaction's earlier operations reach,
adds at most one to every cached height (named premise). -/
def OpDelHtStepOK (p : Params) : Prop :=
  ∀ ts tx, Within p (ts ++ [tx]) → ∀ z top,
    lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z →
    topOf p (ctxOf p ts).view z = .ok top →
    ∀ pre key post, tx.ops = pre ++ Op.del key :: post →
    ∀ r w, (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
    ∀ m, p.H ≤ m → SeenHeightBound m w →
    WriterWP (putKv (.del key)) (ctxOf p ts) w (fun _ v => SeenHeightBound (m + 1) v)

/-- Every operation, from a state that the transaction's earlier operations
reach, adds at most one to every cached height. The run facts come from R. -/
theorem opHtStep_of (p : Params) (hM : 2 ≤ p.M) (R : Struct BVal → Time → Prop)
    (hRL : ∀ P t, R P t → RunLinksOK p P t) (hRK : ∀ P t, R P t → KindsAllOK p P)
    (hRH : ∀ P t, R P t → HeightAllOK p P t) (hchk : OpDelChkOK p) (hdel : OpDelHtStepOK p)
    (ts : List Tx) (tx : Tx) (hw : Within p (ts ++ [tx])) (hr : R (treeRun p ts) ts.length)
    (z : NodeId) (top : Top)
    (hz : lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z)
    (htop : topOf p (ctxOf p ts).view z = .ok top)
    (pre : List Op) (op : Op) (post : List Op) (hsplit : tx.ops = pre ++ op :: post)
    (r : List Bool) (w : W) (hpre : (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w))
    (m : Nat) (hHm : p.H ≤ m) (hs : SeenHeightBound m w) :
    WriterWP (putKv op) (ctxOf p ts) w (fun _ v => SeenHeightBound (m + 1) v) := by
  cases op with
  | del key => exact hdel ts tx hw z top hz htop pre key post hsplit r w hpre m hHm hs
  | put key hv0 =>
    have hR := hRL _ _ hr
    have hvo := viewHtOK_of_run p ts tx hw hR (hRK _ _ hr) (hRH _ _ hr)
    have hi := ht_reached p hM (opHtDelOK_of_chk p hchk) ts tx hw hR hvo z top hz htop pre
      (Op.put key hv0 :: post) hsplit r w hpre
    have hbk := putBook_reached p ts tx hw hR z top htop pre r w hpre
    have hB := putBase_of_run p ts tx hw hR
    exact seenHeight_putKv_put tx.base (appendFrameOK tx.base) key hv0 (ctxOf p ts) w hvo
      (by simp [ctxOf]) hbk.book hi hM hB.wf hbk.klongs m hHm hs

end SIS.Tree
