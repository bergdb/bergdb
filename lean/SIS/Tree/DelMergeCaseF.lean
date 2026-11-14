/-
Case 4 of 024-12's assembly at a reading fuel above the writer's (bergdb 024-22,
024-12's (4), option (a)). A merge inside a delete can space split a full segment
root, one level more, which the delete's root collapse then removes; a state
between them may hold a segment tree of depth p.fuel, which the reading at p.fuel
cannot read through. So the states inside the delete are read at f = p.fuel + 1
(`DelInvF`), and the operation's end at p.fuel again (`getFromR_fuel_mono`), from
the fuel premise of the states before and after the operation. The case is
`OpGetCaseOK'` (`OpGetCaseOK` with the state before the operation fitting the
fuel), and `opGetCaseOK_of'` gives `OpGetCaseOK` from it and `TxSegFitsOK`.
-/
import SIS.Tree.DelMergeCase

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- `OpGetCaseOK` with the state before the operation fitting the fuel too. -/
def OpGetCaseOK' (p : Params) (R : Struct BVal → Time → Prop)
    (P : Ctx → View BVal → W → Op → Prop) : Prop :=
  ∀ ts tx, Within p (ts ++ [tx]) → R (treeRun p ts) ts.length → ∀ z top,
    lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z →
    topOf p (ctxOf p ts).view z = .ok top →
    ∀ pre op post, tx.ops = pre ++ op :: post →
    ∀ r w, (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
    PutInv (ctxOf p ts) (viewOf (treeRun p ts)) w →
    RangeOrder (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey →
    SegFits (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) (p.fuel - 1) w.top.rootKey →
    P (ctxOf p ts) (viewOf (treeRun p ts)) w op →
    WriterWP (putKv op) (ctxOf p ts) w (fun _ w' =>
      SegFits (wNode p (viewOf (treeRun p ts)) w') (ts.length + 1) (p.fuel - 1) w'.top.rootKey →
      ∀ key, keyWf key = true →
        runGet p ts w' key = if op.key == key then op.value else runGet p ts w key)

/-- `OpGetCaseOK` from `OpGetCaseOK'` and the fuel premise along transactions. -/
theorem opGetCaseOK_of' (p : Params) (R : Struct BVal → Time → Prop)
    (P : Ctx → View BVal → W → Op → Prop) (h : OpGetCaseOK' p R P) (hfit : TxSegFitsOK p R) :
    OpGetCaseOK p R P := by
  intro ts tx hw hr z top hz htop pre op post hops r w hpre hI hRO hP
  exact h ts tx hw hr z top hz htop pre op post hops r w hpre hI hRO
    (hfit ts tx hw hr z top hz htop pre (op :: post) hops r w hpre) hP

/-! ## The reading at a fuel f inside the operation (024-12's (4), option (a))

States inside a delete are read at a fuel f above the writer's (f = p.fuel + 1),
so that a merge's root split, which a later collapse undoes, keeps the reading.
`DelInvF` is the delete's invariant at f; the reduction of case (4) on it is
`opGetCaseOK_delMergeF4` (`CollapseCascade.lean`, with the kinds' books of
`DelMergeCaseF3.lean`); the operation's end reads at p.fuel again by
`getFromR_fuel_mono`. -/

/-- The reading at a fuel f above the writer's is the writer's reading for a state
that fits the writer's fuel (`getFromR_fuel_mono`). -/
theorem wGetAt_eq_wGet (c : Ctx) (base : View BVal) (w : W) (f : Nat) (hf : c.p.fuel ≤ f)
    (hwf : ∀ x xn, ReachS (wNode c.p base w) c.i w.top.rootKey x → wNode c.p base w x = some xn →
      klongsWf xn.ks = true)
    (hfit : SegFits (wNode c.p base w) c.i (c.p.fuel - 1) w.top.rootKey) (key : Key) :
    wGetAt c.p c.i base w f key = wGet c.p c.i base w key := by
  have hfp : 1 ≤ c.p.fuel := by unfold Params.fuel; omega
  unfold wGetAt wGet
  exact getFromR_fuel_mono _ _ _ (c.p.fuel - 1) _ hwf hfit f c.p.fuel (by omega) (by omega) key _
    ReachS.root

/-- The delete's reading at f = p.fuel + 1 from the state before it (`DelInvF`)
gives the operation's reading at p.fuel, when the states before and after fit
the writer's fuel. -/
theorem runGet_of_delInvF (p : Params) (ts : List Tx) (w0 v : W) (key : Key)
    (h : DelInvF (ctxOf p ts) (viewOf (treeRun p ts)) w0 key (p.fuel + 1) v)
    (hI0 : PutInv (ctxOf p ts) (viewOf (treeRun p ts)) w0)
    (hF0 : SegFits (wNode p (viewOf (treeRun p ts)) w0) (ts.length + 1) (p.fuel - 1) w0.top.rootKey)
    (hF : SegFits (wNode p (viewOf (treeRun p ts)) v) (ts.length + 1) (p.fuel - 1) v.top.rootKey)
    (key' : Key) (hk : keyWf key' = true) :
    runGet p ts v key' = if key == key' then none else runGet p ts w0 key' := by
  have h1 := wGetAt_eq_wGet (ctxOf p ts) (viewOf (treeRun p ts)) v (p.fuel + 1) (by simp [ctxOf])
    (fun x xn _ hx => h.1.wf x xn hx) hF key'
  have h0 := wGetAt_eq_wGet (ctxOf p ts) (viewOf (treeRun p ts)) w0 (p.fuel + 1) (by simp [ctxOf])
    (fun x xn _ hx => hI0.wf x xn hx) hF0 key'
  have h2 := h.2.2.2.2.2.1 key' hk
  unfold runGet
  show wGet (ctxOf p ts).p (ctxOf p ts).i (viewOf (treeRun p ts)) v key' =
    if key == key' then none else wGet (ctxOf p ts).p (ctxOf p ts).i (viewOf (treeRun p ts)) w0 key'
  rw [← h1, h2, h0]

end SIS.Tree
