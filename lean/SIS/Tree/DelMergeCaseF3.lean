import SIS.Tree.DelMergeCaseF2
import SIS.Tree.RangeMergeRoot
import SIS.Tree.ChildrenKinds
import SIS.Tree.WriterKindsRun

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! Case 4 of 024-12's assembly with the kinds' walk (bergdb 024-12, case (4)):
the reduction of `DelMergeCaseF2.lean` with the delete's inner invariant joined
with the kinds' books (`Book`, `KdInv`; putinv's `kd_merge`, `kd_collapseRoot`,
`kd_descendToHeight`). The walk's ranges after a merge are proved
(`writerWP_merge_range_inv`); its inner children come from the kinds
(`innerChildren_of_kinds`, with the pointers of the run, TP4); the collapse's
inner children from its own invariant (`CollInv`). Left are the merge's
reached nodes and fuel (`MergeStepOKF3`), the collapse's ranges and room
(`CollapseStepOKF3`), and the delete's other steps (`DelStepsOKF3`). -/

/-- The delete's inner invariant with the kinds' books over the book base BK and
the kinds' oracle KO. -/
def DelInvF3 (c : Ctx) (base : View BVal) (w0 : W) (key : Key) (f : Nat) (KO : KindOracle)
    (BK : NodeId) (v : W) : Prop :=
  DelInvF c base w0 key f v ∧ Book BK c v ∧ KdInv KO BK v

/-- Obligation (StepFits for a merge at a fuel f, the take-back's reached nodes):
a merge of the loop, from a state inside a delete with the key access path down
to it (`PathOK`), keeps its reached nodes untaken, and the state after it fits f.
Its ranges and inner children after it are proved (`writerWP_merge_range_inv`,
the kinds). -/
def MergeStepOKF3 (c : Ctx) (base : View BVal) (f : Nat) : Prop :=
  ∀ (w0 : W) (key : Key) (x q : NodeId) (d : Nat) (v : W) (qn xn : KNode)
    (X : Nat → NodeId) (K : Nat → Nat) (Nn : Nat → KNode),
    DelInvF c base w0 key f v → PathOK c v d X K Nn → 0 < d → (v.path[d]?).map (·.2) = some x →
    (v.path[d - 1]?).map (·.2) = some q → v.nodes.lookup q = some qn → qn.leaf = false →
    v.nodes.lookup x = some xn → xn.cnt < c.p.mergeBelow →
    WriterWP (merge x d) c v (fun _ v' =>
      (∀ y, ReachS (wNode c.p base v') c.i v'.top.rootKey y → v'.taken.contains y = false) ∧
      SegFits (wNode c.p base v') c.i (f - 1) v'.top.rootKey)

/-- Obligation (the collapse's ranges and room at a fuel f): `CollapseStepOKF`
with the walk's ranges for `CollRange`; the collapse's inner children are its
own invariant's (`CollInv`). -/
def CollapseStepOKF3 (c : Ctx) (base : View BVal) (f : Nat) : Prop :=
  (∀ w0 v x n leaf ln k, CollGetInvF c base w0 v f →
      RangeOrder (wNode c.p base v) c.i v.top.rootKey → SegDesc c base x v →
      v.nodes.lookup x = some n → n.leaf = false → n.firstTime ≠ some c.i →
      TReach (wNode c.p base v) c.i v.top.rootKey leaf → v.nodes.lookup leaf = some ln →
      ln.leaf = true → (k, x) ∈ ln.liveAt c.i →
      ln.size + 1 + 1 ≤ c.p.M ∧ ∀ y, deadOver c.p (ln.add c.i (.key k y)) = false) ∧
  (∀ w0 v x n only, CollGetInvF c base w0 v f →
      RangeOrder (wNode c.p base v) c.i v.top.rootKey → SegDesc c base x v →
      v.nodes.lookup x = some n → n.leaf = false → n.firstTime = some c.i →
      n.onlyLiveKlong = some only → n.cv? only = some 0 →
      WriterWP (takeBackRoot x (v.path.length - 1) only) c v
        (fun _ v' => RangeOrder (wNode c.p base v') c.i v'.top.rootKey)) ∧
  (∀ w0 v x n only, CollGetInvF c base w0 v f →
      RangeOrder (wNode c.p base v) c.i v.top.rootKey → SegDesc c base x v →
      v.nodes.lookup x = some n → n.leaf = false → n.firstTime ≠ some c.i →
      n.onlyLiveKlong = some only → n.cv? only = some 0 →
      WriterWP (replaceRoot x (v.path.length - 1) only) c v
        (fun _ v' => RangeOrder (wNode c.p base v') c.i v'.top.rootKey))

/-- Inner children from the kinds' walk, kept generic in the context: at the
operation level `innerChildren_of_kinds` gives it, with the pointers of the run. -/
def ICEFromKinds (c : Ctx) (base : View BVal) (KO : KindOracle) (BK : NodeId) : Prop :=
  ∀ v, Book BK c v → KdInv KO BK v →
    (∀ y, TReach (wNode c.p base v) c.i v.top.rootKey y → v.taken.contains y = false) →
    InnerChildrenExist (wNode c.p base v) c.i v.top.rootKey

/-- The collapse keeps `DelInvF3`. -/
theorem writerWP_collapseRoot_delF3 (key : Key) (seg : Nat) (c : Ctx) (base : View BVal)
    (hvc : ViewCoherent c base) (f : Nat) (hf2 : 2 ≤ f) (hC : CollapseStepOKF3 c base f) (w0 : W)
    (k0 : Key) (KO : KindOracle) (BK : NodeId) (hv : ViewIdsBelow BK c.view) (hk : ViewKinds KO BK c)
    (v : W) (hI : DelInvF3 c base w0 k0 f KO BK v) :
    WriterWP (collapseRoot key seg c.p.fuel) c v (fun _ v' => DelInvF3 c base w0 k0 f KO BK v') := by
  obtain ⟨⟨hP, hG, hR, hICE, hF, hread, B, top0, hB, hbook⟩, hbk, hik⟩ := hI
  have hCI : CollGetInvF c base v v f := by
    refine ⟨⟨hP.tree, fun y hy => hP.untaken y (tReach_reachS _ _ _ _ hy),
      fun y yn _ h => hP.times y yn h, fun y yn cc z hy hyn hl hc => hICE y yn cc z hy hyn hl hc⟩,
      fun _ => rfl, hF, fun y yn _ h => hP.wf y yn h, fun y yn _ h => hP.keyNoValue y yn h⟩
  refine writerWP_mono (writerWP_and (writerWP_and (writerWP_collapseRoot_collF f hf2 key seg c base
    hvc v (fun v => RangeOrder (wNode c.p base v) c.i v.top.rootKey)
    (fun v v' hJ hr => by
      show RangeOrder (wNode c.p base v') c.i v'.top.rootKey
      rw [hr.1, hr.2.1]; exact hJ)
    (hC.1 v) (hC.2.1 v) (hC.2.2 v) c.p.fuel v hCI hR)
    (putBook_collapseRoot key seg c.p.fuel c base B top0 hB v hbook))
    (kd_collapseRoot KO BK key seg c.p.fuel c v hv hk hbk hik)) ?_
  rintro _ v' ⟨⟨⟨⟨⟨hT', hu', _, hICE'⟩, hread', hF', _, _⟩, hR'⟩, hbook'⟩, hbk', hik', _⟩
  obtain ⟨hP', hG'⟩ := putInv_after_step c base v' B top0 hB hbook' hT'
    (fun y hy => hu' y (reachS_tReach _ _ _ _ hy)) hR'
  refine ⟨⟨hP', hG', hR', hICE', hF', fun key' hk' => ?_, B, top0, hB, hbook'⟩, hbk', hik'⟩
  rw [hread' key']
  exact hread key' hk'

set_option maxHeartbeats 1600000 in
/-- The merges' loop keeps `DelInvF3`, given the merge's obligation at f: the
descent, the merge's reading and tree, its ranges proved, its inner children
from the kinds. -/
theorem writerWP_mergeUp_delF3 (key : Key) (g : Nat) (c : Ctx) (base : View BVal)
    (hvc : ViewCoherent c base) (fuelR : Nat) (hfR : 2 ≤ fuelR) (hM : MergeStepOKF3 c base fuelR)
    (KO : KindOracle) (BK : NodeId) (hv : ViewIdsBelow BK c.view) (hk : ViewKinds KO BK c)
    (hICEk : ICEFromKinds c base KO BK)
    (hsa2 : 2 ≤ c.p.splitAbove) (hcap : 1 ≤ c.p.mergeMax) (w0 : W) (k0 : Key) :
    ∀ fuel h merged v, DelInvF3 c base w0 k0 fuelR KO BK v →
      WriterWP (mergeUp key g fuel h merged) c v (fun _ v' => DelInvF3 c base w0 k0 fuelR KO BK v') := by
  intro fuel
  induction fuel with
  | zero => intro h merged v _; exact writerWP_throw _ _ _ _
  | succ f ih =>
    intro h merged v ⟨hI, hbk, hik⟩
    unfold mergeUp
    simp only [writerWP_bind, writerWP_read]
    refine writerWP_mono (writerWP_and (descentOKF2 c base fuelR w0 k0 key g h v hI)
      (kd_descendToHeight KO BK key g h c v hv hk hbk hik)) ?_
    intro d v1 ⟨⟨hI1, hPF⟩, hbk1, hik1, _⟩
    split
    · simp only [writerWP_pure]; exact ⟨hI1, hbk1, hik1⟩
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
          · simp only [writerWP_pure]; exact ⟨hI2, hbk2, hik2⟩
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
            · simp only [writerWP_pure]; exact ⟨hI3, hbk3, hik3⟩
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
              have hmg := writerWP_merge_get_invF2 fuelR hfR ex.2 d c base hvc v3 hI3.1 hI3.2.1 hI3.2.2.1
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
              have hI4 : DelInvF c base w0 k0 fuelR v4 :=
                ⟨hP4, hG4, hR4, hICE4, hF4, fun key' hk' => by
                  rw [hread4 hF4 key']; exact hI3.2.2.2.2.2.1 key' hk', B1, t1, hB1, hb4⟩
              split
              · simp only [writerWP_pure]; exact ⟨hI4, hbk4, hik4⟩
              · exact ih (h + 1) true v4 ⟨hI4, hbk4, hik4⟩

/-- `afterDelete` keeps `DelInvF3`, given the merge's and the collapse's
obligations at f. -/
theorem writerWP_afterDelete_delF3 (key : Key) (g h : Nat) (c : Ctx) (base : View BVal)
    (hvc : ViewCoherent c base) (fuelR : Nat) (hfR : 2 ≤ fuelR) (hM : MergeStepOKF3 c base fuelR)
    (hC : CollapseStepOKF3 c base fuelR)
    (KO : KindOracle) (BK : NodeId) (hv : ViewIdsBelow BK c.view) (hk : ViewKinds KO BK c)
    (hICEk : ICEFromKinds c base KO BK) (hsa2 : 2 ≤ c.p.splitAbove)
    (hcap : 1 ≤ c.p.mergeMax) (w0 : W) (k0 : Key) (v : W) (hI : DelInvF3 c base w0 k0 fuelR KO BK v) :
    WriterWP (afterDelete key g h) c v (fun _ v' => DelInvF3 c base w0 k0 fuelR KO BK v') :=
  writerWP_afterDelete_inv key g h c (DelInvF3 c base w0 k0 fuelR KO BK)
    (fun v hI => writerWP_mergeUp_delF3 key g c base hvc fuelR hfR hM KO BK hv hk hICEk hsa2 hcap w0 k0
      c.p.fuel h false v hI)
    (fun v hI => writerWP_collapseRoot_delF3 key g c base hvc fuelR hfR hC w0 k0 KO BK hv hk v hI) v hI

/-- Obligation (the delete's other steps, with the kinds' books): `DelStepsOKF`
with the merges' loop, `afterDelete` and the collapse keeping `DelInvF3` over the
transaction's base and the run's kinds. -/
def DelStepsOKF3 (p : Params) (R : Struct BVal → Time → Prop) : Prop :=
  ∀ ts tx, Within p (ts ++ [tx]) → R (treeRun p ts) ts.length → ∀ z top,
    lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z →
    topOf p (ctxOf p ts).view z = .ok top →
    ∀ pre op post, tx.ops = pre ++ op :: post →
    ∀ r w, (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
    PutInv (ctxOf p ts) (viewOf (treeRun p ts)) w →
    RangeOrder (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey →
    SegFits (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) (p.fuel - 1) w.top.rootKey →
    ∀ key, op = .del key → p.merges = true →
    (∀ g h v, DelInvF3 (ctxOf p ts) (viewOf (treeRun p ts)) w key (p.fuel + 1)
        (kindOracleOf p (treeRun p ts)) tx.base v →
      WriterWP (afterDelete key g h) (ctxOf p ts) v
        (fun _ v' => DelInvF3 (ctxOf p ts) (viewOf (treeRun p ts)) w key (p.fuel + 1)
          (kindOracleOf p (treeRun p ts)) tx.base v')) →
    (∀ g h merged v, DelInvF3 (ctxOf p ts) (viewOf (treeRun p ts)) w key (p.fuel + 1)
        (kindOracleOf p (treeRun p ts)) tx.base v →
      WriterWP (mergeUp key g p.fuel h merged) (ctxOf p ts) v
        (fun _ v' => DelInvF3 (ctxOf p ts) (viewOf (treeRun p ts)) w key (p.fuel + 1)
          (kindOracleOf p (treeRun p ts)) tx.base v')) →
    (∀ seg v, DelInvF3 (ctxOf p ts) (viewOf (treeRun p ts)) w key (p.fuel + 1)
        (kindOracleOf p (treeRun p ts)) tx.base v →
      WriterWP (collapseRoot key seg p.fuel) (ctxOf p ts) v
        (fun _ v' => DelInvF3 (ctxOf p ts) (viewOf (treeRun p ts)) w key (p.fuel + 1)
          (kindOracleOf p (treeRun p ts)) tx.base v')) →
    WriterWP (putKv op) (ctxOf p ts) w (fun _ w' =>
      SegFits (wNode p (viewOf (treeRun p ts)) w') (ts.length + 1) (p.fuel - 1) w'.top.rootKey →
      ∀ key', keyWf key' = true →
        runGet p ts w' key' = if op.key == key' then op.value else runGet p ts w key')

/-- Case 4 at the reading fuel p.fuel + 1 inside the delete, with the kinds'
books: `OpGetCaseOK'` from the merge's, the collapse's and the other steps'
obligations, given the pointers of every run within reach (TP4, for the kinds;
`innerChildren_reached` takes it too). -/
theorem opGetCaseOK'_delMerge3 (p : Params) (R : Struct BVal → Time → Prop) (hS : DelStepsOKF3 p R)
    (hM : ∀ ts, MergeStepOKF3 (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1))
    (hC : ∀ ts, CollapseStepOKF3 (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1))
    (hsa2 : 2 ≤ p.splitAbove) (hcap : 1 ≤ p.mergeMax) (hMM : 2 ≤ p.M)
    (hPtr : ∀ ts, Within p ts → PointersOK (treeRun p ts)) :
    OpGetCaseOK' p R DelMergeCase := by
  have hf2 : 2 ≤ p.fuel + 1 := by unfold Params.fuel; omega
  intro ts tx hw hr z top hz htop pre op post hops r w hpre hI hRO hF0 hP
  obtain ⟨key, hop, hmerges⟩ := hP
  have hwts : Within p ts := by
    have := within_take p (ts ++ [tx]) hw ts.length
    simpa using this
  have hfresh : ∀ q ∈ treeRun p ts, q.1 < tx.base := by
    have := (hw.2 ts.length (by simp)).1
    simpa using this
  have hK := treeRun_kindsAllOK p hMM hPtr ts hwts
  have hv : ViewIdsBelow tx.base (ctxOf p ts).view :=
    viewIdsBelow_rootless _ _ (viewIdsBelow_view p (treeRun p ts) ts.length tx.base hfresh)
  have hk : ViewKinds (kindOracleOf p (treeRun p ts)) tx.base (ctxOf p ts) :=
    viewKinds_of p (treeRun p ts) ts.length tx.base hfresh (treeRun_timesLE p ts) (hPtr ts hwts) hK
  have hICEk : ICEFromKinds (ctxOf p ts) (viewOf (treeRun p ts)) (kindOracleOf p (treeRun p ts)) tx.base :=
    fun v hb hi hun => innerChildren_of_kinds p (treeRun p ts) tx.base (ctxOf p ts) v rfl hK
      (hPtr ts hwts) hb hi.cache hun
  exact hS ts tx hw hr z top hz htop pre op post hops r w hpre hI hRO hF0 key hop hmerges
    (fun g h v hv' => writerWP_afterDelete_delF3 key g h (ctxOf p ts) _ (viewCoherent_ctxOf p ts)
      (p.fuel + 1) hf2 (hM ts) (hC ts) _ _ hv hk hICEk hsa2 hcap w key v hv')
    (fun g h merged v hv' => writerWP_mergeUp_delF3 key g (ctxOf p ts) _ (viewCoherent_ctxOf p ts)
      (p.fuel + 1) hf2 (hM ts) _ _ hv hk hICEk hsa2 hcap w key p.fuel h merged v hv')
    (fun seg v hv' => writerWP_collapseRoot_delF3 key seg (ctxOf p ts) _ (viewCoherent_ctxOf p ts)
      (p.fuel + 1) hf2 (hC ts) w key _ _ hv hk v hv')

/-- Case 4 (`OpGetCaseOK`) from the merge's, the collapse's and the other steps'
obligations with the kinds' books, the fuel premise along transactions
(`TxSegFitsOK`) and the pointers of every run within reach (TP4). -/
theorem opGetCaseOK_delMergeF3 (p : Params) (R : Struct BVal → Time → Prop) (hS : DelStepsOKF3 p R)
    (hM : ∀ ts, MergeStepOKF3 (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1))
    (hC : ∀ ts, CollapseStepOKF3 (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1))
    (hsa2 : 2 ≤ p.splitAbove) (hcap : 1 ≤ p.mergeMax) (hMM : 2 ≤ p.M)
    (hPtr : ∀ ts, Within p ts → PointersOK (treeRun p ts)) (hfit : TxSegFitsOK p R) :
    OpGetCaseOK p R DelMergeCase :=
  opGetCaseOK_of' p R DelMergeCase (opGetCaseOK'_delMerge3 p R hS hM hC hsa2 hcap hMM hPtr) hfit

end SIS.Tree
