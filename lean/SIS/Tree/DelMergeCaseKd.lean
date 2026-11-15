import SIS.Tree.GetDescentOK
import SIS.Tree.RangeMergeRoot
import SIS.Tree.ChildrenKinds
import SIS.Tree.WriterKindsRun
import SIS.Tree.RangeCollapseSeg

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! Case 4 of 024-12's assembly with the kinds' walk (bergdb 024-12, case (4)):
the delete's inner invariant joined with the kinds' books (`DelInv`: `Book`,
`KdInv`; putinv's `kd_merge`, `kd_collapseRoot`, `kd_descendToHeight`). The
walk's ranges after a merge are proved (`writerWP_merge_range_inv`); its inner
children come from the kinds (`innerChildren_of_kinds`, with the pointers of
the run, TP4). The merges' loop keeps `DelInv` given the merge's obligation
(`writerWP_mergeUp_del`, `MergeStepOK`); `DelStepsOK` is the delete's
other steps. Case (4) itself is `opGetCaseOK_delMerge` (`CollapseCascade.lean`),
whose collapse takes a full segment leaf; an earlier route with the collapse's
room premise was removed. -/

/-- The delete's inner invariant with the kinds' books over the book base BK and
the kinds' oracle KO. -/
def DelInv (c : Ctx) (base : View BVal) (w0 : W) (key : Key) (f : Nat) (KO : KindOracle)
    (BK : NodeId) (v : W) : Prop :=
  DelInvF c base w0 key f v ∧ Book BK c v ∧ KdInv KO BK v

/-- `DelInv` with no fit and no reading: the writer's tree with its books and kinds. -/
def DelInvT (c : Ctx) (base : View BVal) (KO : KindOracle) (BK : NodeId) (v : W) : Prop :=
  PutInv c base v ∧ PutInvG c base v ∧ RangeOrder (wNode c.p base v) c.i v.top.rootKey ∧
  InnerChildrenExist (wNode c.p base v) c.i v.top.rootKey ∧
  (∃ B top0, PutBase c base B ∧ PutBook c B top0 v) ∧ Book BK c v ∧ KdInv KO BK v

/-- `DelInv` at any fuel gives its tree's facts. -/
theorem delInvT_of_delInv (c : Ctx) (base : View BVal) (w0 : W) (key : Key) (f : Nat)
    (KO : KindOracle) (BK : NodeId) (v : W) (h : DelInv c base w0 key f KO BK v) :
    DelInvT c base KO BK v := by
  obtain ⟨⟨hP, hG, hR, hICE, _, _, hbk⟩, hb, hk⟩ := h
  exact ⟨hP, hG, hR, hICE, hbk, hb, hk⟩

/-- Obligation (StepFits for a merge at a fuel f, the take-back's reached nodes):
a merge of the loop, from a state inside a delete with the key access path down
to it (`PathOK`), keeps its reached nodes untaken, and the state after it fits f.
Its ranges and inner children after it are proved (`writerWP_merge_range_inv`,
the kinds). -/
def MergeStepOK (c : Ctx) (base : View BVal) (f : Nat) : Prop :=
  ∀ (w0 : W) (key : Key) (x q : NodeId) (d : Nat) (v : W) (qn xn : KNode)
    (X : Nat → NodeId) (K : Nat → Nat) (Nn : Nat → KNode),
    DelInvF c base w0 key f v → PathOK c v d X K Nn → 0 < d → (v.path[d]?).map (·.2) = some x →
    (v.path[d - 1]?).map (·.2) = some q → v.nodes.lookup q = some qn → qn.leaf = false →
    v.nodes.lookup x = some xn → xn.cnt < c.p.mergeBelow →
    WriterWP (merge x d) c v (fun _ v' =>
      (∀ y, ReachS (wNode c.p base v') c.i v'.top.rootKey y → v'.taken.contains y = false) ∧
      SegFits (wNode c.p base v') c.i (f - 1) v'.top.rootKey)

/-- Inner children from the kinds' walk, kept generic in the context: at the
operation level `innerChildren_of_kinds` gives it, with the pointers of the run. -/
def ICEFromKinds (c : Ctx) (base : View BVal) (KO : KindOracle) (BK : NodeId) : Prop :=
  ∀ v, Book BK c v → KdInv KO BK v →
    (∀ y, TReach (wNode c.p base v) c.i v.top.rootKey y → v.taken.contains y = false) →
    InnerChildrenExist (wNode c.p base v) c.i v.top.rootKey

/-- `MergeStepOK` with the fit at the merge's end asked only where a condition C
on the state there holds and the state has `PutInv` (bergdb 025-05, route P). With
C true it is `MergeStepOK` (`mergeStepOKW_of`); with C "the next id below f" it
holds for every state, by the pigeonhole bound (`mergeStepOKW_next`, FuelNext.lean). -/
def MergeStepOKW (c : Ctx) (base : View BVal) (f : Nat) (C : W → Prop) : Prop :=
  ∀ (w0 : W) (key : Key) (x q : NodeId) (d : Nat) (v : W) (qn xn : KNode)
    (X : Nat → NodeId) (K : Nat → Nat) (Nn : Nat → KNode),
    DelInvF c base w0 key f v → PathOK c v d X K Nn → 0 < d → (v.path[d]?).map (·.2) = some x →
    (v.path[d - 1]?).map (·.2) = some q → v.nodes.lookup q = some qn → qn.leaf = false →
    v.nodes.lookup x = some xn → xn.cnt < c.p.mergeBelow →
    WriterWP (merge x d) c v (fun _ v' =>
      (∀ y, ReachS (wNode c.p base v') c.i v'.top.rootKey y → v'.taken.contains y = false) ∧
      (C v' → PutInv c base v' → SegFits (wNode c.p base v') c.i (f - 1) v'.top.rootKey))

theorem mergeStepOKW_of (c : Ctx) (base : View BVal) (f : Nat) (C : W → Prop)
    (h : MergeStepOK c base f) : MergeStepOKW c base f C :=
  fun w0 key x q d v qn xn X K Nn h1 h2 h3 h4 h5 h6 h7 h8 h9 =>
    writerWP_mono (h w0 key x q d v qn xn X K Nn h1 h2 h3 h4 h5 h6 h7 h8 h9)
      (fun _ _ hv => ⟨hv.1, fun _ _ => hv.2⟩)

/-- The delete's invariant at f while a condition C holds (bergdb 025-05, route P):
the fresh ids' books always, and `DelInv` at f where C holds. -/
def DelInvW (c : Ctx) (base : View BVal) (w0 : W) (key : Key) (f : Nat) (C : W → Prop)
    (KO : KindOracle) (BK : NodeId) (v : W) : Prop :=
  (∃ B, ViewIdsBelow B c.view ∧ FreshCache B v) ∧ (C v → DelInv c base w0 key f KO BK v)

theorem delInvW_of_delInv (c : Ctx) (base : View BVal) (w0 : W) (key : Key) (f : Nat) (C : W → Prop)
    (KO : KindOracle) (BK : NodeId) (v : W) (h : DelInv c base w0 key f KO BK v) :
    DelInvW c base w0 key f C KO BK v := by
  obtain ⟨B, _, hB, hb⟩ := h.1.2.2.2.2.2.2
  exact ⟨⟨B, hB.good.ids, hb.fresh⟩, fun _ => h⟩

set_option maxHeartbeats 1600000 in
/-- The merges' loop keeps `DelInvW` for a condition C that holds at a state if
it holds at a later one with a larger next id (bergdb 025-05, route P): the
descent, the merge's reading and tree, its ranges proved, its inner children from
the kinds, the fit at the merge's end from `MergeStepOKW`. Where C fails, the
fresh ids' books alone (`freshCache_mergeUp`). -/
theorem writerWP_mergeUp_delW (key : Key) (g : Nat) (c : Ctx) (base : View BVal)
    (hvc : ViewCoherent c base) (fuelR : Nat) (hfR : 2 ≤ fuelR) (C : W → Prop)
    (hC : ∀ v v', v.next ≤ v'.next → C v' → C v) (hM : MergeStepOKW c base fuelR C)
    (KO : KindOracle) (BK : NodeId) (hv : ViewIdsBelow BK c.view) (hk : ViewKinds KO BK c)
    (hICEk : ICEFromKinds c base KO BK)
    (hsa2 : 2 ≤ c.p.splitAbove) (hcap : 1 ≤ c.p.mergeMax) (w0 : W) (k0 : Key) :
    ∀ fuel h merged v, DelInvW c base w0 k0 fuelR C KO BK v →
      WriterWP (mergeUp key g fuel h merged) c v (fun _ v' => DelInvW c base w0 k0 fuelR C KO BK v') := by
  intro fuel
  induction fuel with
  | zero => intro h merged v _; exact writerWP_throw _ _ _ _
  | succ f ih =>
    intro h merged v ⟨⟨B0, hB0v, hfc⟩, hD⟩
    by_cases hno : ¬ C v
    · refine writerWP_mono (freshCache_mergeUp key g (f + 1) h merged c v hB0v hfc) ?_
      rintro _ v' ⟨hf', hle⟩
      exact ⟨⟨B0, hB0v, hf'⟩, fun hC' => absurd (hC v v' hle hC') hno⟩
    obtain ⟨hI, hbk, hik⟩ := hD (Classical.byContradiction hno)
    unfold mergeUp
    simp only [writerWP_bind, writerWP_read]
    refine writerWP_mono (writerWP_and (descentOK c base fuelR w0 k0 key g h v hI)
      (kd_descendToHeight KO BK key g h c v hv hk hbk hik)) ?_
    intro d v1 ⟨⟨hI1, hPF⟩, hbk1, hik1, _⟩
    split
    · simp only [writerWP_pure]; exact delInvW_of_delInv c base w0 k0 fuelR C KO BK _ ⟨hI1, hbk1, hik1⟩
    · rename_i hd0
      have hd : 0 < d := by
        cases d with
        | zero => simp at hd0
        | succ _ => omega
      obtain ⟨X, K, Nn, hP1⟩ := hPF
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
          refine writerWP_mono (writerWP_and (writerWP_and (writerWP_and
            (writerWP_getNode_all eq.2 c v1 base hvc) (writerWP_getNode_cache eq.2 c v1))
            (putBook_getNode eq.2 c base B1 t1 hB1 v1 hb1))
            (kd_getNode KO BK eq.2 c v1 hv hk hbk1 hik1)) ?_
          rintro qn v2 ⟨⟨⟨⟨hr2, hl2, _, hpre2, _⟩, _, _, hp2⟩, hb2⟩, hbk2, hik2, _⟩
          have hI2 := delInvF_of_readsAs c base w0 k0 fuelR v1 v2 hI1 hr2 ⟨B1, t1, hB1, hb2⟩
          have hkeep2 : ∀ z zn, v1.nodes.lookup z = some zn → v2.nodes.lookup z = some zn :=
            fun z zn h => lookup_of_prefix _ _ hpre2 _ _ h
          have hP2 := pathOK_transport c v1 v2 d X K Nn hP1 hp2 hkeep2 hr2.2.2.1 hr2.2.1
          split
          · simp only [writerWP_pure]; exact delInvW_of_delInv c base w0 k0 fuelR C KO BK _ ⟨hI2, hbk2, hik2⟩
          · rename_i hql
            have hql' : qn.leaf = false := by simpa using hql
            rw [writerWP_bind]
            refine writerWP_mono (writerWP_and (writerWP_and (writerWP_and
              (writerWP_getNode_all ex.2 c v2 base hvc) (writerWP_getNode_cache ex.2 c v2))
              (putBook_getNode ex.2 c base B1 t1 hB1 v2 hb2))
              (kd_getNode KO BK ex.2 c v2 hv hk hbk2 hik2)) ?_
            rintro xn v3 ⟨⟨⟨⟨hr3, hl3, _, hpre3, _⟩, _, _, hp3⟩, hb3⟩, hbk3, hik3, _⟩
            have hI3 := delInvF_of_readsAs c base w0 k0 fuelR v2 v3 hI2 hr3 ⟨B1, t1, hB1, hb3⟩
            have hkeep3 : ∀ z zn, v2.nodes.lookup z = some zn → v3.nodes.lookup z = some zn :=
              fun z zn h => lookup_of_prefix _ _ hpre3 _ _ h
            have hP3 := pathOK_transport c v2 v3 d X K Nn hP2 hp3 hkeep3 hr3.2.2.1 hr3.2.1
            split
            · simp only [writerWP_pure]; exact delInvW_of_delInv c base w0 k0 fuelR C KO BK _ ⟨hI3, hbk3, hik3⟩
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
              have hmg := writerWP_merge_get_inv fuelR hfR ex.2 d c base hvc v3 hI3.1 hI3.2.1 hI3.2.2.1
                X K Nn hP3 hd hxX (by rw [hqn]; exact hql') hsa2 hcap
              have hms := hM w0 k0 ex.2 eq.2 d v3 qn xn X K Nn hI3 hP3 hd (by rw [hp3, hp2, hex]; rfl)
                (by rw [hp3, hp2, heq]; rfl) (hkeep3 _ _ hl2) hql' hl3 hcnt'
              have htr := writerWP_merge_tree_inv2 ex.2 d c base hvc v3 hI3.1 hI3.2.1 hI3.2.2.1 X K Nn hP3
                hd hxX (by rw [hqn]; exact hql') hsa2 hcap
              have hrg := writerWP_merge_range_inv ex.2 d c base hvc v3 hI3.1 hI3.2.1 hI3.2.2.1 X K Nn hP3
                hd hxX (by rw [hqn]; exact hql') hsa2 hcap
              have hkd := kd_merge KO BK ex.2 d c v3 hv hk hbk3 hik3 (by omega) ex.1
                (by rw [hp3, hp2, hex]) (by
                  intro a q' hq'
                  rw [hp3, hp2, heq] at hq'
                  simp only [Option.some.injEq] at hq'
                  subst hq'
                  exact ⟨qn, hkeep3 _ _ hl2, hql'⟩)
              refine writerWP_mono (writerWP_and (writerWP_and (writerWP_and (writerWP_and
                (writerWP_and hmg hms) (putBook_merge ex.2 d c base B1 t1 hB1 v3 hb3)) htr) hrg) hkd) ?_
              rintro r v4 ⟨⟨⟨⟨⟨hread4, hu4, hF4⟩, hb4⟩, hT4⟩, hR4⟩, hbk4, hik4, _, _⟩
              obtain ⟨hP4, hG4⟩ := putInv_after_step c base v4 B1 t1 hB1 hb4 hT4 hu4 hR4
              have hICE4 := hICEk v4 hbk4 hik4 (fun y hy => hu4 y (tReach_reachS _ _ _ _ hy))
              have hQ4 : DelInvW c base w0 k0 fuelR C KO BK v4 := by
                refine ⟨⟨B1, hB1.good.ids, hb4.fresh⟩, fun hC4 => ?_⟩
                have hF4' := hF4 hC4 hP4
                exact ⟨⟨hP4, hG4, hR4, hICE4, hF4', fun key' hk' => by
                  rw [hread4 hF4' key']; exact hI3.2.2.2.2.2.1 key' hk', B1, t1, hB1, hb4⟩, hbk4, hik4⟩
              split
              · simp only [writerWP_pure]; exact hQ4
              · exact ih (h + 1) true v4 hQ4

/-- The merges' loop keeps `DelInv`, given the merge's obligation at f: the
descent, the merge's reading and tree, its ranges proved, its inner children
from the kinds. -/
theorem writerWP_mergeUp_del (key : Key) (g : Nat) (c : Ctx) (base : View BVal)
    (hvc : ViewCoherent c base) (fuelR : Nat) (hfR : 2 ≤ fuelR) (hM : MergeStepOK c base fuelR)
    (KO : KindOracle) (BK : NodeId) (hv : ViewIdsBelow BK c.view) (hk : ViewKinds KO BK c)
    (hICEk : ICEFromKinds c base KO BK)
    (hsa2 : 2 ≤ c.p.splitAbove) (hcap : 1 ≤ c.p.mergeMax) (w0 : W) (k0 : Key) :
    ∀ fuel h merged v, DelInv c base w0 k0 fuelR KO BK v →
      WriterWP (mergeUp key g fuel h merged) c v (fun _ v' => DelInv c base w0 k0 fuelR KO BK v') :=
  fun fuel h merged v hI => writerWP_mono
    (writerWP_mergeUp_delW key g c base hvc fuelR hfR (fun _ => True) (fun _ _ _ _ => trivial)
      (mergeStepOKW_of c base fuelR _ hM) KO BK hv hk hICEk hsa2 hcap w0 k0 fuel h merged v
      (delInvW_of_delInv c base w0 k0 fuelR _ KO BK v hI))
    (fun _ _ hv' => hv'.2 trivial)

/-- Obligation (the delete's other steps, with the kinds' books): `DelStepsOKF`
with the merges' loop, `afterDelete` and the collapse keeping `DelInv` over the
transaction's base and the run's kinds. -/
def DelStepsOK (p : Params) (R : Struct BVal → Time → Prop) : Prop :=
  ∀ ts tx, Within p (ts ++ [tx]) → R (treeRun p ts) ts.length → ∀ z top,
    lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z →
    topOf p (ctxOf p ts).view z = .ok top →
    ∀ pre op post, tx.ops = pre ++ op :: post →
    ∀ r w, (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
    PutInv (ctxOf p ts) (viewOf (treeRun p ts)) w →
    RangeOrder (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey →
    SegFits (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) (p.fuel - 1) w.top.rootKey →
    ∀ key, op = .del key → p.merges = true →
    (∀ g h v, DelInv (ctxOf p ts) (viewOf (treeRun p ts)) w key (p.fuel + 1)
        (kindOracleOf p (treeRun p ts)) tx.base v →
      WriterWP (afterDelete key g h) (ctxOf p ts) v
        (fun _ v' => DelInv (ctxOf p ts) (viewOf (treeRun p ts)) w key (p.fuel + 1)
          (kindOracleOf p (treeRun p ts)) tx.base v')) →
    (∀ g h merged v, DelInv (ctxOf p ts) (viewOf (treeRun p ts)) w key (p.fuel + 1)
        (kindOracleOf p (treeRun p ts)) tx.base v →
      WriterWP (mergeUp key g p.fuel h merged) (ctxOf p ts) v
        (fun _ v' => DelInv (ctxOf p ts) (viewOf (treeRun p ts)) w key (p.fuel + 1)
          (kindOracleOf p (treeRun p ts)) tx.base v')) →
    (∀ seg v, DelInv (ctxOf p ts) (viewOf (treeRun p ts)) w key (p.fuel + 1)
        (kindOracleOf p (treeRun p ts)) tx.base v →
      WriterWP (collapseRoot key seg p.fuel) (ctxOf p ts) v
        (fun _ v' => DelInv (ctxOf p ts) (viewOf (treeRun p ts)) w key (p.fuel + 1)
          (kindOracleOf p (treeRun p ts)) tx.base v')) →
    WriterWP (putKv op) (ctxOf p ts) w (fun _ w' =>
      SegFits (wNode p (viewOf (treeRun p ts)) w') (ts.length + 1) (p.fuel - 1) w'.top.rootKey →
      ∀ key', keyWf key' = true →
        runGet p ts w' key' = if op.key == key' then op.value else runGet p ts w key')

end SIS.Tree
