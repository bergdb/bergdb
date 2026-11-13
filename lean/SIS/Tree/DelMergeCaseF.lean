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

/-- Obligation (the collapse's ranges at a fuel f): the collapse's steps keep the
walk's ranges and inner children, and a segment leaf has room for a replaced
root's klong (`writerWP_collapseRoot_collF`'s premises). -/
def CollapseStepOKF (c : Ctx) (base : View BVal) (f : Nat) : Prop :=
  (∀ w0 v x n leaf ln k, CollGetInvF c base w0 v f → CollRange c base v → SegDesc c base x v →
      v.nodes.lookup x = some n → n.leaf = false → n.firstTime ≠ some c.i →
      TReach (wNode c.p base v) c.i v.top.rootKey leaf → v.nodes.lookup leaf = some ln →
      ln.leaf = true → (k, x) ∈ ln.liveAt c.i →
      ln.size + 1 + 1 ≤ c.p.M ∧ ∀ y, deadOver c.p (ln.add c.i (.key k y)) = false) ∧
  (∀ w0 v x n only, CollGetInvF c base w0 v f → CollRange c base v → SegDesc c base x v →
      v.nodes.lookup x = some n → n.leaf = false → n.firstTime = some c.i →
      n.onlyLiveKlong = some only → n.cv? only = some 0 →
      WriterWP (takeBackRoot x (v.path.length - 1) only) c v (fun _ v' => CollRange c base v')) ∧
  (∀ w0 v x n only, CollGetInvF c base w0 v f → CollRange c base v → SegDesc c base x v →
      v.nodes.lookup x = some n → n.leaf = false → n.firstTime ≠ some c.i →
      n.onlyLiveKlong = some only → n.cv? only = some 0 →
      WriterWP (replaceRoot x (v.path.length - 1) only) c v (fun _ v' => CollRange c base v'))

/-- The collapse keeps `DelInvF`. -/
theorem writerWP_collapseRoot_delF (key : Key) (seg : Nat) (c : Ctx) (base : View BVal)
    (hvc : ViewCoherent c base) (f : Nat) (hf2 : 2 ≤ f) (hC : CollapseStepOKF c base f) (w0 : W)
    (k0 : Key) (v : W) (hI : DelInvF c base w0 k0 f v) :
    WriterWP (collapseRoot key seg c.p.fuel) c v (fun _ v' => DelInvF c base w0 k0 f v') := by
  obtain ⟨hP, hG, hR, hICE, hF, hread, B, top0, hB, hbook⟩ := hI
  have hCI : CollGetInvF c base v v f := by
    refine ⟨⟨hP.tree, fun y hy => hP.untaken y (tReach_reachS _ _ _ _ hy),
      fun y yn _ h => hP.times y yn h, fun y yn cc z hy hyn hl hc => hICE y yn cc z hy hyn hl hc⟩,
      fun _ => rfl, hF, fun y yn _ h => hP.wf y yn h, fun y yn _ h => hP.keyNoValue y yn h⟩
  refine writerWP_mono (writerWP_and (writerWP_collapseRoot_collF f hf2 key seg c base hvc v
    (CollRange c base)
    (fun v v' hJ hr => ⟨by rw [hr.1, hr.2.1]; exact hJ.1, by rw [hr.1, hr.2.1]; exact hJ.2⟩)
    (hC.1 v) (hC.2.1 v) (hC.2.2 v) c.p.fuel v hCI ⟨hR, hICE⟩)
    (putBook_collapseRoot key seg c.p.fuel c base B top0 hB v hbook)) ?_
  rintro _ v' ⟨⟨⟨⟨hT', hu', _, _⟩, hread', hF', _, _⟩, hR', hICE'⟩, hbook'⟩
  obtain ⟨hP', hG'⟩ := putInv_after_step c base v' B top0 hB hbook' hT'
    (fun y hy => hu' y (reachS_tReach _ _ _ _ hy)) hR'
  refine ⟨hP', hG', hR', hICE', hF', fun key' hk => ?_, B, top0, hB, hbook'⟩
  rw [hread' key']
  exact hread key' hk

/-- Obligation (StepFits for a merge at a fuel f, the take-back's reached nodes, the
ranges): a merge of the loop, from a state inside a delete, keeps `StepInv`, and
the state after it fits f. -/
def MergeStepOKF (c : Ctx) (base : View BVal) (f : Nat) : Prop :=
  ∀ (w0 : W) (key : Key) (x q : NodeId) (d : Nat) (v : W) (qn xn : KNode),
    DelInvF c base w0 key f v → 0 < d → (v.path[d]?).map (·.2) = some x →
    (v.path[d - 1]?).map (·.2) = some q → v.nodes.lookup q = some qn → qn.leaf = false →
    v.nodes.lookup x = some xn → xn.cnt < c.p.mergeBelow →
    WriterWP (merge x d) c v (fun _ v' => StepInv c base v' ∧
      SegFits (wNode c.p base v') c.i (f - 1) v'.top.rootKey)

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

/-- Obligation (the delete's other steps): with the merges' steps keeping `DelInvF` at
f = p.fuel + 1, and the state before the operation fitting the fuel: the delete's
steps put the state inside the operation into `DelInvF`, and its end reads at
p.fuel (`runGet`) by `getFromR_fuel_mono`. -/
def DelStepsOKF (p : Params) (R : Struct BVal → Time → Prop) : Prop :=
  ∀ ts tx, Within p (ts ++ [tx]) → R (treeRun p ts) ts.length → ∀ z top,
    lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z →
    topOf p (ctxOf p ts).view z = .ok top →
    ∀ pre op post, tx.ops = pre ++ op :: post →
    ∀ r w, (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
    PutInv (ctxOf p ts) (viewOf (treeRun p ts)) w →
    RangeOrder (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey →
    SegFits (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) (p.fuel - 1) w.top.rootKey →
    ∀ key, op = .del key → p.merges = true →
    (∀ g h v, DelInvF (ctxOf p ts) (viewOf (treeRun p ts)) w key (p.fuel + 1) v →
      WriterWP (afterDelete key g h) (ctxOf p ts) v
        (fun _ v' => DelInvF (ctxOf p ts) (viewOf (treeRun p ts)) w key (p.fuel + 1) v')) →
    (∀ g h merged v, DelInvF (ctxOf p ts) (viewOf (treeRun p ts)) w key (p.fuel + 1) v →
      WriterWP (mergeUp key g p.fuel h merged) (ctxOf p ts) v
        (fun _ v' => DelInvF (ctxOf p ts) (viewOf (treeRun p ts)) w key (p.fuel + 1) v')) →
    (∀ seg v, DelInvF (ctxOf p ts) (viewOf (treeRun p ts)) w key (p.fuel + 1) v →
      WriterWP (collapseRoot key seg p.fuel) (ctxOf p ts) v
        (fun _ v' => DelInvF (ctxOf p ts) (viewOf (treeRun p ts)) w key (p.fuel + 1) v')) →
    WriterWP (putKv op) (ctxOf p ts) w (fun _ w' =>
      SegFits (wNode p (viewOf (treeRun p ts)) w') (ts.length + 1) (p.fuel - 1) w'.top.rootKey →
      ∀ key', keyWf key' = true →
        runGet p ts w' key' = if op.key == key' then op.value else runGet p ts w key')

end SIS.Tree
