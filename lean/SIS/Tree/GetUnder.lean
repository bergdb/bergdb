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
holds after every run within reach. `RunReadOK` is the premise that the
writer's refinement of the map needs as far as known: TP7's invariant at the
latest time, its pointers, its key nodes sound as they are (`KeyNodesOK`), and
TREE for key nodes (`KeyTreeOK`), which TP7's invariant lacks
(`sharedSegment_changes_other_key`). -/

/-- TREE for key nodes at time t: two klongs live at t in key nodes reachable
then name one node only if they are one klong. -/
def KeyTreeOK (p : Params) (P : Struct BVal) (t : Time) : Prop :=
  ∀ x1 ∈ keyNodesAt p P t, ∀ x2 ∈ keyNodesAt p P t, ∀ n1 n2,
    keyNodeAt p P x1 = some n1 → keyNodeAt p P x2 = some n2 →
    ∀ q1 ∈ n1.liveAt t, ∀ q2 ∈ n2.liveAt t, q1.2 = q2.2 → x1 = x2 ∧ q1.1 = q2.1

/-- The soundness of the structure before a transaction that the writer's
refinement of the map needs: TP7's invariant at its time, its pointers, its key
nodes sound as they are, and TREE for its key nodes. -/
def RunReadOK (p : Params) (P : Struct BVal) (t : Time) : Prop :=
  InvOK p P t ∧ PointersOK P ∧ KeyNodesOK p P ∧ KeyTreeOK p P t

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

theorem opGetOKUnder_mono (p : Params) (R R' : Struct BVal → Time → Prop)
    (h : ∀ P t, R P t → R' P t) (ho : OpGetOKUnder p R') : OpGetOKUnder p R :=
  fun ts tx hw hr => ho ts tx hw (h _ _ hr)

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

/-- TP10 from TP7, the key nodes sound as they are and TREE after every run
within reach, and the two statements about the writer under `RunReadOK`. -/
theorem getOK_of_runRead (p : Params) (hinv : InvPreserved p)
    (hK : ∀ ts, Within p ts →
      KeyNodesOK p (treeRun p ts) ∧ KeyTreeOK p (treeRun p ts) ts.length)
    (ho : OpGetOKUnder p (RunReadOK p)) (hl : OverlayLiftOKUnder p (RunReadOK p)) : GetOK p :=
  getOK_of_under p hinv (RunReadOK p)
    (fun ts hw => ⟨(hinv ts hw ts.length (Nat.le_refl _)).1,
      (hinv ts hw ts.length (Nat.le_refl _)).2, (hK ts hw).1, (hK ts hw).2⟩) ho hl

/-- TP11 from TP7, the key nodes sound as they are and TREE after every run
within reach, and the two statements about the writer under `RunReadOK`. -/
theorem scanOK_of_runRead (p : Params) (hinv : InvPreserved p)
    (hK : ∀ ts, Within p ts →
      KeyNodesOK p (treeRun p ts) ∧ KeyTreeOK p (treeRun p ts) ts.length)
    (ho : OpGetOKUnder p (RunReadOK p)) (hl : OverlayLiftOKUnder p (RunReadOK p)) : ScanOK p :=
  scanOK_of_under p hinv (RunReadOK p)
    (fun ts hw => ⟨(hinv ts hw ts.length (Nat.le_refl _)).1,
      (hinv ts hw ts.length (Nat.le_refl _)).2, (hK ts hw).1, (hK ts hw).2⟩) ho hl

end SIS.Tree
