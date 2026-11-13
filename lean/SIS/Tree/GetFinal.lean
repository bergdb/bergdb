import SIS.Tree.GetDelSplit
import SIS.Tree.PutInvRun

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! TP10 and TP11 from the writer's invariant inside a transaction (bergdb
024-12): `OpGetOKUnder` follows from `PutInv` at every state the writer reaches
(putinv's `putInv_reached`, from `OpPutInvOK` and cost's `OpTreeOK`) and from
`OpGetPutInvOK`, the statement that every operation from a state that meets
`PutInv` changes the reading by itself alone. The rules of `GetLeafRoot.lean`,
`GetLeafBelow.lean`, `GetSegLeaf.lean`, `GetChain.lean`, `GetInnerSplit.lean`,
`GetSpaceSpace.lean` and `GetDelSplit.lean` prove `OpGetPutInvOK`'s cases. -/

/-- Every operation of a transaction within reach, from a state that its
earlier operations reach and that meets `PutInv`, changes the reading by itself
alone. -/
def OpGetPutInvOK (p : Params) (R : Struct BVal → Time → Prop) : Prop :=
  ∀ ts tx, Within p (ts ++ [tx]) → R (treeRun p ts) ts.length → ∀ z top,
    lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z →
    topOf p (ctxOf p ts).view z = .ok top →
    ∀ pre op post, tx.ops = pre ++ op :: post →
    ∀ r w, (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
    PutInv (ctxOf p ts) (viewOf (treeRun p ts)) w →
    WriterWP (putKv op) (ctxOf p ts) w (fun _ w' => ∀ key, keyWf key = true →
      runGet p ts w' key = if op.key == key then op.value else runGet p ts w key)

/-- `OpGetOKUnder` from `OpGetPutInvOK`, putinv's `OpPutInvOK` and cost's
`OpTreeOK`, for a run premise R that gives the run's links, P's tree and TP7's
invariant. -/
theorem opGetOKUnder_of_putInv (p : Params) (R : Struct BVal → Time → Prop)
    (hRL : ∀ P t, R P t → RunLinksOK p P t) (hRT : ∀ P t, R P t → TreeAt p P t)
    (hRI : ∀ P t, R P t → InvOK p P t)
    (ho : OpTreeOK p) (hP : OpPutInvOK p R) (hg : OpGetPutInvOK p R) : OpGetOKUnder p R := by
  intro ts tx hw hr z top hz htop pre op post hsplit r w hpre
  exact hg ts tx hw hr z top hz htop pre op post hsplit r w hpre
    (putInv_reached p R hRL ho hP ts tx hw hr (hRT _ _ hr) (hRI _ _ hr) z top hz htop pre
      (op :: post) hsplit r w hpre)

/-- TP10 from TP7, a run premise R that every run within reach meets and that
gives the run's links, P's tree and TP7's invariant, cost's `OpTreeOK`,
putinv's `OpPutInvOK`, `OpGetPutInvOK`, and tp7's lift under R. -/
theorem getOK_of_putInv (p : Params) (hinv : InvPreserved p) (R : Struct BVal → Time → Prop)
    (hR : ∀ ts, Within p ts → R (treeRun p ts) ts.length)
    (hRL : ∀ P t, R P t → RunLinksOK p P t) (hRT : ∀ P t, R P t → TreeAt p P t)
    (hRI : ∀ P t, R P t → InvOK p P t)
    (ho : OpTreeOK p) (hP : OpPutInvOK p R) (hg : OpGetPutInvOK p R)
    (hl : OverlayLiftOKUnder p R) : GetOK p :=
  getOK_of_under p hinv R hR (opGetOKUnder_of_putInv p R hRL hRT hRI ho hP hg) hl

/-- TP11 from the same premises as `getOK_of_putInv`. -/
theorem scanOK_of_putInv (p : Params) (hinv : InvPreserved p) (R : Struct BVal → Time → Prop)
    (hR : ∀ ts, Within p ts → R (treeRun p ts) ts.length)
    (hRL : ∀ P t, R P t → RunLinksOK p P t) (hRT : ∀ P t, R P t → TreeAt p P t)
    (hRI : ∀ P t, R P t → InvOK p P t)
    (ho : OpTreeOK p) (hP : OpPutInvOK p R) (hg : OpGetPutInvOK p R)
    (hl : OverlayLiftOKUnder p R) : ScanOK p :=
  scanOK_of_under p hinv R hR (opGetOKUnder_of_putInv p R hRL hRT hRI ho hP hg) hl

end SIS.Tree
