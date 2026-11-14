import SIS.Tree.GetFrame
import SIS.Tree.InvLatest

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! `OpGetOK` and `OverlayLiftOK` with premises on the structure before the
transaction (bergdb 024-12, TP10). As first stated they quantify over every
run within reach and ask nothing of its structure, so a proof would have to
show first that no such structure is malformed. These forms take the
structure's soundness as a premise R, any premise; TP10 and TP11 follow when R
holds after every run within reach. The writer's refinement of the map needs,
as far as known, TP7's invariant at the latest time, its pointers, its key nodes
sound as they are (`KeyNodesOK`), and TREE for key nodes, which TP7's invariant
lacks. -/

/-- `OpGetOK` for transactions after a run whose structure meets R. -/
def OpGetOKUnder (p : Params) (R : Struct BVal → Time → Prop) : Prop :=
  ∀ ts tx, Within p (ts ++ [tx]) → R (treeRun p ts) ts.length → ∀ z top,
    lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z →
    topOf p (ctxOf p ts).view z = .ok top →
    ∀ pre op post, tx.ops = pre ++ op :: post →
    ∀ r w, (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
    WriterWP (putKv op) (ctxOf p ts) w (fun _ w' => ∀ key, keyWf key = true →
      runGet p ts w' key = if op.key == key then op.value else runGet p ts w key)

/-- `OverlayLiftOK` for transactions after a run whose structure meets R. -/
def OverlayLiftOKUnder (p : Params) (R : Struct BVal → Time → Prop) : Prop :=
  ∀ ts tx, Within p (ts ++ [tx]) → R (treeRun p ts) ts.length → ∀ noops w,
    runOps p tx.base tx.ops (ts.length + 1) (view (treeSpec p) (treeRun p ts) ts.length) =
      .ok (noops, w) →
    (∀ x n, w.nodes.lookup x = some n → w.taken.contains x = false →
      knodeOf p (viewOf (treeRun p (ts ++ [tx]))) x = some n) ∧
    (∀ x ∈ w.taken, tx.base ≤ x) ∧
    (w.newTop = true → w.taken.contains w.top.id = false)

theorem overlayLiftOKUnder_mono (p : Params) (R R' : Struct BVal → Time → Prop)
    (h : ∀ P t, R P t → R' P t) (hl : OverlayLiftOKUnder p R') : OverlayLiftOKUnder p R :=
  fun ts tx hw hr => hl ts tx hw (h _ _ hr)

theorem opGetOK_of_under (p : Params) (R : Struct BVal → Time → Prop)
    (hR : ∀ ts, Within p ts → R (treeRun p ts) ts.length) (ho : OpGetOKUnder p R) :
    OpGetOK p :=
  fun ts tx hw => ho ts tx hw (hR ts (within_snoc_prefix p ts tx hw))

theorem overlayLiftOK_of_under (p : Params) (R : Struct BVal → Time → Prop)
    (hR : ∀ ts, Within p ts → R (treeRun p ts) ts.length) (hl : OverlayLiftOKUnder p R) :
    OverlayLiftOK p :=
  fun ts tx hw => hl ts tx hw (hR ts (within_snoc_prefix p ts tx hw))

/-- TP10 from TP7, a premise R that every run within reach meets, and the two
statements about the writer under R. -/
theorem getOK_of_under (p : Params) (hinv : InvPreserved p) (R : Struct BVal → Time → Prop)
    (hR : ∀ ts, Within p ts → R (treeRun p ts) ts.length) (ho : OpGetOKUnder p R)
    (hl : OverlayLiftOKUnder p R) : GetOK p :=
  getOK_of_op_overlay p hinv (opGetOK_of_under p R hR ho)
    (overlayLiftOK_of_under p R hR hl)

/-- TP11 from TP7, a premise R that every run within reach meets, and the two
statements about the writer under R. -/
theorem scanOK_of_under (p : Params) (hinv : InvPreserved p) (R : Struct BVal → Time → Prop)
    (hR : ∀ ts, Within p ts → R (treeRun p ts) ts.length) (ho : OpGetOKUnder p R)
    (hl : OverlayLiftOKUnder p R) : ScanOK p :=
  scanOK_of_op_overlay p hinv (opGetOK_of_under p R hR ho)
    (overlayLiftOK_of_under p R hR hl)

end SIS.Tree
