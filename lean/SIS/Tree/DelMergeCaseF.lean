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
`DelInvF`, `MergeStepOKF`, `DescentOKF`, `CollapseStepOKF` and `DelStepsOKF` are
the obligations of the reduction at f; the operation's end reads at p.fuel again
by `getFromR_fuel_mono`. -/

/-- `CollapseStepOK` at a fuel f. -/
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

/-- `MergeStepOK` at a fuel f: the state after the merge fits f. -/
def MergeStepOKF (c : Ctx) (base : View BVal) (f : Nat) : Prop :=
  ∀ (w0 : W) (key : Key) (x q : NodeId) (d : Nat) (v : W) (qn xn : KNode),
    DelInvF c base w0 key f v → 0 < d → (v.path[d]?).map (·.2) = some x →
    (v.path[d - 1]?).map (·.2) = some q → v.nodes.lookup q = some qn → qn.leaf = false →
    v.nodes.lookup x = some xn → xn.cnt < c.p.mergeBelow →
    WriterWP (merge x d) c v (fun _ v' => StepInv c base v' ∧
      SegFits (wNode c.p base v') c.i (f - 1) v'.top.rootKey)

/-- `DescentOK` at a fuel f. -/
def DescentOKF (c : Ctx) (base : View BVal) (f : Nat) : Prop :=
  ∀ (w0 : W) (k0 key : Key) (g h : Nat) (v : W), DelInvF c base w0 k0 f v →
    WriterWP (descendToHeight key g h) c v (fun d v' => DelInvF c base w0 k0 f v' ∧
      (0 < d → ∃ X K Nn, PathOK c v' d X K Nn ∧ MergePathCond c X K Nn d))

/-- The merges' loop keeps `DelInvF`, given the obligations at f. -/
theorem writerWP_mergeUp_delF (key : Key) (g : Nat) (c : Ctx) (base : View BVal)
    (hvc : ViewCoherent c base) (fuelR : Nat) (hfR : 2 ≤ fuelR) (hM : MergeStepOKF c base fuelR)
    (hD : DescentOKF c base fuelR)
    (hsa2 : 2 ≤ c.p.splitAbove) (hcap : 1 ≤ c.p.mergeMax) (w0 : W) (k0 : Key) :
    ∀ fuel h merged v, DelInvF c base w0 k0 fuelR v →
      WriterWP (mergeUp key g fuel h merged) c v (fun _ v' => DelInvF c base w0 k0 fuelR v') := by
  intro fuel
  induction fuel with
  | zero => intro h merged v _; exact writerWP_throw _ _ _ _
  | succ f ih =>
    intro h merged v hI
    unfold mergeUp
    simp only [writerWP_bind, writerWP_read]
    refine writerWP_mono (hD w0 k0 key g h v hI) ?_
    intro d v1 ⟨hI1, hPF⟩
    split
    · simp only [writerWP_pure]; exact hI1
    · rename_i hd0
      have hd : 0 < d := by
        cases d with
        | zero => simp at hd0
        | succ _ => omega
      obtain ⟨X, K, Nn, hP1, hcond⟩ := hPF hd
      unfold pathNode
      simp only [writerWP_bind, writerWP_get]
      cases hex : v1.path[d]? with
      | none => exact writerWP_throw _ _ _ _
      | some ex =>
        simp only [writerWP_pure]
        cases heq : v1.path[d - 1]? with
        | none => exact writerWP_throw _ _ _ _
        | some eq =>
          simp only [writerWP_pure]
          obtain ⟨B1, t1, hB1, hb1⟩ := hI1.2.2.2.2.2.2
          refine writerWP_mono (writerWP_and (writerWP_and (writerWP_getNode_all eq.2 c v1 base hvc)
            (writerWP_getNode_cache eq.2 c v1)) (putBook_getNode eq.2 c base B1 t1 hB1 v1 hb1)) ?_
          rintro qn v2 ⟨⟨⟨hr2, hl2, _, hpre2, _⟩, _, _, hp2⟩, hb2⟩
          have hI2 := delInvF_of_readsAs c base w0 k0 fuelR v1 v2 hI1 hr2 ⟨B1, t1, hB1, hb2⟩
          have hkeep2 : ∀ z zn, v1.nodes.lookup z = some zn → v2.nodes.lookup z = some zn :=
            fun z zn h => lookup_of_prefix _ _ hpre2 _ _ h
          have hP2 := pathOK_transport c v1 v2 d X K Nn hP1 hp2 hkeep2 hr2.2.2.1 hr2.2.1
          split
          · simp only [writerWP_pure]; exact hI2
          · rename_i hql
            have hql' : qn.leaf = false := by simpa using hql
            rw [writerWP_bind]
            refine writerWP_mono (writerWP_and (writerWP_and (writerWP_getNode_all ex.2 c v2 base hvc)
              (writerWP_getNode_cache ex.2 c v2)) (putBook_getNode ex.2 c base B1 t1 hB1 v2 hb2)) ?_
            rintro xn v3 ⟨⟨⟨hr3, hl3, _, hpre3, _⟩, _, _, hp3⟩, hb3⟩
            have hI3 := delInvF_of_readsAs c base w0 k0 fuelR v2 v3 hI2 hr3 ⟨B1, t1, hB1, hb3⟩
            have hkeep3 : ∀ z zn, v2.nodes.lookup z = some zn → v3.nodes.lookup z = some zn :=
              fun z zn h => lookup_of_prefix _ _ hpre3 _ _ h
            have hP3 := pathOK_transport c v2 v3 d X K Nn hP2 hp3 hkeep3 hr3.2.2.1 hr3.2.1
            split
            · simp only [writerWP_pure]; exact hI3
            · rename_i hcnt
              have hcnt' : xn.cnt < c.p.mergeBelow := by simpa using hcnt
              rw [writerWP_bind]
              obtain ⟨hX3, _, hS23, _, _⟩ := id hP3
              have hxX : X d = ex.2 := by
                have := hX3 d (Nat.le_refl _)
                rw [hp3, hp2, hex] at this
                exact (Option.some.inj this).symm
              have hqX : X (d - 1) = eq.2 := by
                have := hX3 (d - 1) (by omega)
                rw [hp3, hp2, heq] at this
                exact (Option.some.inj this).symm
              have hqn : Nn (d - 1) = qn := by
                have h1 := (hS23 (d - 1) (by omega)).1
                rw [hqX, hkeep3 _ _ hl2] at h1
                exact (Option.some.inj h1).symm
              obtain ⟨hc1, hc2, hc3⟩ := hcond
              have hmg := writerWP_merge_get_invF fuelR hfR ex.2 d c base hvc v3 hI3.1 hI3.2.1 hI3.2.2.1 X K Nn hP3 hd
                hxX (by rw [hqn]; exact hql') hsa2 hcap hc1 hc2 hc3
              have hms := hM w0 k0 ex.2 eq.2 d v3 qn xn hI3 hd (by rw [hp3, hp2, hex]; rfl)
                (by rw [hp3, hp2, heq]; rfl) (hkeep3 _ _ hl2) hql' hl3 hcnt'
              have htr := writerWP_merge_tree_inv ex.2 d c base hvc v3 hI3.1 hI3.2.1 hI3.2.2.1 X K Nn hP3 hd
                hxX (by rw [hqn]; exact hql') hsa2 hcap hc3
              refine writerWP_mono (writerWP_and (writerWP_and (writerWP_and hmg hms)
                (putBook_merge ex.2 d c base B1 t1 hB1 v3 hb3)) htr) ?_
              rintro r v4 ⟨⟨⟨hread4, ⟨hu4, hR4, hICE4⟩, hF4⟩, hb4⟩, hT4⟩
              obtain ⟨hP4, hG4⟩ := putInv_after_step c base v4 B1 t1 hB1 hb4 hT4 hu4 hR4
              have hI4 : DelInvF c base w0 k0 fuelR v4 :=
                ⟨hP4, hG4, hR4, hICE4, hF4, fun key' hk => by rw [hread4 hF4 key']; exact hI3.2.2.2.2.2.1 key' hk,
                  B1, t1, hB1, hb4⟩
              split
              · simp only [writerWP_pure]; exact hI4
              · exact ih (h + 1) true v4 hI4


/-- `afterDelete` keeps `DelInvF`, given the obligations at f. -/
theorem writerWP_afterDelete_delF (key : Key) (g h : Nat) (c : Ctx) (base : View BVal)
    (hvc : ViewCoherent c base) (fuelR : Nat) (hfR : 2 ≤ fuelR) (hM : MergeStepOKF c base fuelR)
    (hD : DescentOKF c base fuelR) (hC : CollapseStepOKF c base fuelR) (hsa2 : 2 ≤ c.p.splitAbove)
    (hcap : 1 ≤ c.p.mergeMax) (w0 : W) (k0 : Key) (v : W) (hI : DelInvF c base w0 k0 fuelR v) :
    WriterWP (afterDelete key g h) c v (fun _ v' => DelInvF c base w0 k0 fuelR v') :=
  writerWP_afterDelete_inv key g h c (DelInvF c base w0 k0 fuelR)
    (fun v hI => writerWP_mergeUp_delF key g c base hvc fuelR hfR hM hD hsa2 hcap w0 k0 c.p.fuel h false v hI)
    (fun v hI => writerWP_collapseRoot_delF key g c base hvc fuelR hfR hC w0 k0 v hI) v hI

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

/-- The obligation `DelStepsOK` with the merges' steps keeping `DelInvF` at
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

/-- Case 4 at the reading fuel p.fuel + 1 inside the delete (option (a)):
`OpGetCaseOK'` from the obligations at f = p.fuel + 1. -/
theorem opGetCaseOK'_delMerge (p : Params) (R : Struct BVal → Time → Prop) (hS : DelStepsOKF p R)
    (hM : ∀ ts, MergeStepOKF (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1))
    (hD : ∀ ts, DescentOKF (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1))
    (hC : ∀ ts, CollapseStepOKF (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1))
    (hsa2 : 2 ≤ p.splitAbove) (hcap : 1 ≤ p.mergeMax) :
    OpGetCaseOK' p R DelMergeCase := by
  have hf2 : 2 ≤ p.fuel + 1 := by unfold Params.fuel; omega
  intro ts tx hw hr z top hz htop pre op post hops r w hpre hI hRO hF0 hP
  obtain ⟨key, hop, hmerges⟩ := hP
  exact hS ts tx hw hr z top hz htop pre op post hops r w hpre hI hRO hF0 key hop hmerges
    (fun g h v hv => writerWP_afterDelete_delF key g h (ctxOf p ts) _ (viewCoherent_ctxOf p ts)
      (p.fuel + 1) hf2 (hM ts) (hD ts) (hC ts) hsa2 hcap w key v hv)
    (fun g h merged v hv => writerWP_mergeUp_delF key g (ctxOf p ts) _ (viewCoherent_ctxOf p ts)
      (p.fuel + 1) hf2 (hM ts) (hD ts) hsa2 hcap w key p.fuel h merged v hv)
    (fun seg v hv => writerWP_collapseRoot_delF key seg (ctxOf p ts) _ (viewCoherent_ctxOf p ts)
      (p.fuel + 1) hf2 (hC ts) w key v hv)

/-- Case 4 (`OpGetCaseOK`) from the obligations at p.fuel + 1 and the fuel premise
along transactions (`TxSegFitsOK`). -/
theorem opGetCaseOK_delMergeF (p : Params) (R : Struct BVal → Time → Prop) (hS : DelStepsOKF p R)
    (hM : ∀ ts, MergeStepOKF (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1))
    (hD : ∀ ts, DescentOKF (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1))
    (hC : ∀ ts, CollapseStepOKF (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1))
    (hsa2 : 2 ≤ p.splitAbove) (hcap : 1 ≤ p.mergeMax) (hfit : TxSegFitsOK p R) :
    OpGetCaseOK p R DelMergeCase :=
  opGetCaseOK_of' p R DelMergeCase (opGetCaseOK'_delMerge p R hS hM hD hC hsa2 hcap) hfit

end SIS.Tree
