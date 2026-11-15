/-
The first stratum of bergdb 025-05, part 2 (`htb` out, step 7): inside a delete,
an invariant with no fit and no reading, for the joint induction's members whose
conclusions speak of no fuel (`QdW`, `TakeJ2`, the checked copies).

Route P (FuelNext.lean) reads the writer's tree at every fuel above p.fuel and
the next id (`DelInvA`), so the merges' loop and root collapse need no fit. Its
families still enter that invariant from `DelInv` at p.fuel + 1 at the state
after the leaf's change, which asks the fit p.fuel - 1 at the delete's start
(`delInvA_of_delInv`), and that fit is what `htb` gives.

In the stratum the reading is not needed at all. So the leaf's change need give
only the tree's facts (`DelInvT`: `PutInv`, the ranges, the inner children, the
books and the kinds). Route P's invariant then holds at that state taken as its
own reference, with a key that no read asks (`[]`, not well formed): its fit at
every fuel above the next id is P1, and its reading clause says the state reads
as itself (`delInvA_self`). The loops keep `DelInvA` for every reference, so the
invariant with the reference left open (`DelInvAE`) is kept by `afterDelete`,
the merges' loop and root collapse with no fit, and gives `QdW` at the end. The
same for the take-back's facts (`DelInvJT`, `DelInvJAE`) and for the state at a
call of `afterDelete` in the checked copies (`DelHoleJE`).
-/
import SIS.Tree.FuelNext

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! ## The tree's facts of the delete's invariant -/

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

/-- No read asks the key `[]`. -/
theorem nil_beq_of_keyWf (key' : Key) (hk : keyWf key' = true) : (([] : Key) == key') = false := by
  cases key' with
  | nil => simp [keyWf] at hk
  | cons a l => rfl

/-- The tree's facts give route P's invariant at the state taken as its own
reference, with the key `[]`: the fit at every fuel above the next id by P1, the
reading clause the state's reading itself. -/
theorem delInvA_self (c : Ctx) (base : View BVal) (KO : KindOracle) (BK : NodeId) (v : W)
    (h : DelInvT c base KO BK v) : DelInvA c base v [] KO BK v := by
  obtain ⟨hP, hG, hR, hICE, hbk, hb, hk⟩ := h
  intro F _ hn
  refine ⟨⟨hP, hG, hR, hICE, segFits_mono _ _ _ _ _ (segFits_next_of_putInv c base v hP) (by omega),
    fun key' hk' => ?_, hbk⟩, hb, hk⟩
  rw [nil_beq_of_keyWf key' hk']
  rfl

/-- Route P's invariant with the reference left open. -/
def DelInvAE (c : Ctx) (base : View BVal) (KO : KindOracle) (BK : NodeId) (v : W) : Prop :=
  ∃ u, DelInvA c base u [] KO BK v

theorem delInvAE_of_T (c : Ctx) (base : View BVal) (KO : KindOracle) (BK : NodeId) (v : W)
    (h : DelInvT c base KO BK v) : DelInvAE c base KO BK v :=
  ⟨v, delInvA_self c base KO BK v h⟩

/-- `DelInvA` at any reference gives the tree's facts. -/
theorem delInvT_of_delInvA (c : Ctx) (base : View BVal) (w0 : W) (k0 : Key) (KO : KindOracle)
    (BK : NodeId) (v : W) (h : DelInvA c base w0 k0 KO BK v) : DelInvT c base KO BK v := by
  obtain ⟨F, hF, hn⟩ := exists_fuel_above c v
  exact delInvT_of_delInv c base w0 k0 F KO BK v (h F hF hn)

theorem delInvT_of_delInvAE (c : Ctx) (base : View BVal) (KO : KindOracle) (BK : NodeId) (v : W)
    (h : DelInvAE c base KO BK v) : DelInvT c base KO BK v := by
  obtain ⟨u, hu⟩ := h
  exact delInvT_of_delInvA c base u [] KO BK v hu

/-- `DelInvAE` gives `QdW`, which speaks of no fuel. -/
theorem qdW_of_delInvAE (p : Params) (ts : List Tx) (KO : KindOracle) (BK : NodeId) (v : W)
    (h : DelInvAE (ctxOf p ts) (viewOf (treeRun p ts)) KO BK v) : QdW p ts v := by
  obtain ⟨u, hu⟩ := h
  exact qdW_of_delInvA p ts u [] KO BK v hu

/-- The merges' loop keeps `DelInvAE`, with no fit premise. -/
theorem writerWP_mergeUp_delAE (key : Key) (g : Nat) (c : Ctx) (base : View BVal)
    (hvc : ViewCoherent c base) (hpos : 0 < c.i)
    (KO : KindOracle) (BK : NodeId) (hv : ViewIdsBelow BK c.view) (hk : ViewKinds KO BK c)
    (hICEk : ICEFromKinds c base KO BK) (hsa2 : 2 ≤ c.p.splitAbove) (hcap : 1 ≤ c.p.mergeMax) :
    ∀ fuel h merged v, DelInvAE c base KO BK v →
      WriterWP (mergeUp key g fuel h merged) c v (fun _ v' => DelInvAE c base KO BK v') := by
  intro fuel h merged v ⟨u, hu⟩
  exact writerWP_mono (writerWP_mergeUp_delA key g c base hvc hpos KO BK hv hk hICEk hsa2 hcap u []
    fuel h merged v hu) (fun _ v' h' => ⟨u, h'⟩)

/-- Root collapse keeps `DelInvAE`, with no fit premise. -/
theorem writerWP_collapseRoot_delAE (key : Key) (seg : Nat) (c : Ctx) (base : View BVal)
    (hvc : ViewCoherent c base) (KO : KindOracle) (BK : NodeId)
    (hv : ViewIdsBelow BK c.view) (hk : ViewKinds KO BK c) (hICEk : ICEFromKinds c base KO BK)
    (hsa2 : 2 ≤ c.p.splitAbove) (v : W) (hA : DelInvAE c base KO BK v) :
    WriterWP (collapseRoot key seg c.p.fuel) c v (fun _ v' => DelInvAE c base KO BK v') := by
  obtain ⟨u, hu⟩ := hA
  exact writerWP_mono (writerWP_collapseRoot_delA key seg c base hvc u [] KO BK hv hk hICEk hsa2 v hu)
    (fun _ v' h' => ⟨u, h'⟩)

/-- `afterDelete` keeps `DelInvAE`, with no fit premise. -/
theorem writerWP_afterDelete_delAE (key : Key) (g h : Nat) (c : Ctx) (base : View BVal)
    (hvc : ViewCoherent c base) (hpos : 0 < c.i) (KO : KindOracle) (BK : NodeId)
    (hv : ViewIdsBelow BK c.view) (hk : ViewKinds KO BK c) (hICEk : ICEFromKinds c base KO BK)
    (hsa2 : 2 ≤ c.p.splitAbove) (hcap : 1 ≤ c.p.mergeMax) (v : W) (hA : DelInvAE c base KO BK v) :
    WriterWP (afterDelete key g h) c v (fun _ v' => DelInvAE c base KO BK v') := by
  obtain ⟨u, hu⟩ := hA
  exact writerWP_mono (writerWP_afterDelete_delA key g h c base hvc hpos KO BK hv hk hICEk hsa2 hcap u []
    v hu) (fun _ v' h' => ⟨u, h'⟩)

/-! ## The take-back's facts -/

/-- `DelInvJ` with no fit and no reading. -/
def DelInvJT (c : Ctx) (base : View BVal) (KO : KindOracle) (BK B : NodeId) (v : W) : Prop :=
  DelInvT c base KO BK v ∧ TakeJ2 c base B v ∧ B ≤ v.next

theorem delInvJT_of_delInvJ (c : Ctx) (base : View BVal) (w0 : W) (key : Key) (f : Nat)
    (KO : KindOracle) (BK B : NodeId) (v : W) (h : DelInvJ c base w0 key f KO BK B v) :
    DelInvJT c base KO BK B v :=
  ⟨delInvT_of_delInv c base w0 key f KO BK v h.1, h.2.1, h.2.2⟩

theorem delInvJA_self (c : Ctx) (base : View BVal) (KO : KindOracle) (BK B : NodeId) (v : W)
    (h : DelInvJT c base KO BK B v) : DelInvJA c base v [] KO BK B v :=
  fun F hF hn => ⟨delInvA_self c base KO BK v h.1 F hF hn, h.2.1, h.2.2⟩

/-- `DelInvJA` with the reference left open. -/
def DelInvJAE (c : Ctx) (base : View BVal) (KO : KindOracle) (BK B : NodeId) (v : W) : Prop :=
  ∃ u, DelInvJA c base u [] KO BK B v

theorem delInvJAE_of_T (c : Ctx) (base : View BVal) (KO : KindOracle) (BK B : NodeId) (v : W)
    (h : DelInvJT c base KO BK B v) : DelInvJAE c base KO BK B v :=
  ⟨v, delInvJA_self c base KO BK B v h⟩

theorem takeJ2_of_delInvJAE (c : Ctx) (base : View BVal) (KO : KindOracle) (BK B : NodeId) (v : W)
    (h : DelInvJAE c base KO BK B v) : TakeJ2 c base B v := by
  obtain ⟨u, hu⟩ := h
  exact takeJ2_of_delInvJA c base u [] KO BK B v hu

/-- `DelInvJAE` gives `DelInvAE`. -/
theorem delInvAE_of_JAE (c : Ctx) (base : View BVal) (KO : KindOracle) (BK B : NodeId) (v : W)
    (h : DelInvJAE c base KO BK B v) : DelInvAE c base KO BK v := by
  obtain ⟨u, hu⟩ := h
  exact ⟨u, fun F hF hn => (hu F hF hn).1⟩

theorem writerWP_mergeUp_delJAE (key : Key) (g : Nat) (c : Ctx) (base : View BVal)
    (hvc : ViewCoherent c base) (hpos : 0 < c.i)
    (KO : KindOracle) (BK : NodeId) (hv : ViewIdsBelow BK c.view) (hk : ViewKinds KO BK c)
    (hICEk : ICEFromKinds c base KO BK) (hsa2 : 2 ≤ c.p.splitAbove) (hcap : 1 ≤ c.p.mergeMax)
    (B : NodeId) :
    ∀ fuel h merged v, DelInvJAE c base KO BK B v →
      WriterWP (mergeUp key g fuel h merged) c v (fun _ v' => DelInvJAE c base KO BK B v') := by
  intro fuel h merged v ⟨u, hu⟩
  exact writerWP_mono (writerWP_mergeUp_delJA key g c base hvc hpos KO BK hv hk hICEk hsa2 hcap B u []
    fuel h merged v hu) (fun _ v' h' => ⟨u, h'⟩)

theorem writerWP_collapseRoot_delJAE (key : Key) (seg : Nat) (c : Ctx) (base : View BVal)
    (hvc : ViewCoherent c base) (KO : KindOracle) (BK : NodeId)
    (hv : ViewIdsBelow BK c.view) (hk : ViewKinds KO BK c) (hICEk : ICEFromKinds c base KO BK)
    (hsa2 : 2 ≤ c.p.splitAbove) (B : NodeId) (hpos : 0 < c.i) (v : W)
    (hA : DelInvJAE c base KO BK B v) :
    WriterWP (collapseRoot key seg c.p.fuel) c v (fun _ v' => DelInvJAE c base KO BK B v') := by
  obtain ⟨u, hu⟩ := hA
  exact writerWP_mono (writerWP_collapseRoot_delJA key seg c base hvc u [] KO BK hv hk hICEk hsa2 B hpos
    v hu) (fun _ v' h' => ⟨u, h'⟩)

theorem writerWP_afterDelete_delJAE (key : Key) (g h : Nat) (c : Ctx) (base : View BVal)
    (hvc : ViewCoherent c base) (hpos : 0 < c.i) (KO : KindOracle) (BK : NodeId)
    (hv : ViewIdsBelow BK c.view) (hk : ViewKinds KO BK c) (hICEk : ICEFromKinds c base KO BK)
    (hsa2 : 2 ≤ c.p.splitAbove) (hcap : 1 ≤ c.p.mergeMax) (B : NodeId) (v : W)
    (hA : DelInvJAE c base KO BK B v) :
    WriterWP (afterDelete key g h) c v (fun _ v' => DelInvJAE c base KO BK B v') := by
  obtain ⟨u, hu⟩ := hA
  exact writerWP_mono (writerWP_afterDelete_delJA key g h c base hvc hpos KO BK hv hk hICEk hsa2 hcap B u []
    v hu) (fun _ v' h' => ⟨u, h'⟩)

/-! ## The checked copies: the merges' loop and `afterDelete` from `DelInvJAE` -/

theorem rwp_mergeUp_of_JAE (key : Key) (g : Nat) (c : Ctx) (base : View BVal)
    (hvc : ViewCoherent c base) (KO : KindOracle) (B : NodeId) (hv : ViewIdsBelow B c.view)
    (hk : ViewKinds KO B c) (hICEk : ICEFromKinds c base KO B) (hsa2 : 2 ≤ c.p.splitAbove)
    (hcap : 1 ≤ c.p.mergeMax) (hpos : 0 < c.i) (hvg : ViewGood B c) (hkv : ViewKlongsWf c.p c.view)
    (top0 : Top) (hB : PutBase c base B) :
    ∀ fuel h merged v, DelInvJAE c base KO B B v → PutBook c B top0 v →
      RWP (mergeUp key g fuel h merged) (mergeUpChk key g fuel h merged) c v := by
  intro fuel h merged v ⟨u, hu⟩ hb
  exact rwp_mergeUp_of_JA key g c base hvc KO B hv hk hICEk hsa2 hcap hpos hvg hkv top0 hB u []
    fuel h merged v hu hb

theorem rwp_afterDelete_of_JAE (key : Key) (g h : Nat) (c : Ctx) (base : View BVal)
    (hvc : ViewCoherent c base) (hpos : 0 < c.i) (KO : KindOracle) (B : NodeId)
    (hv : ViewIdsBelow B c.view) (hk : ViewKinds KO B c) (hICEk : ICEFromKinds c base KO B)
    (hsa2 : 2 ≤ c.p.splitAbove) (hcap : 1 ≤ c.p.mergeMax) (top0 : Top) (hB : PutBase c base B)
    (v : W) (hA : DelInvJAE c base KO B B v) (hb : PutBook c B top0 v)
    (hmu : RWP (mergeUp key g c.p.fuel h false) (mergeUpChk key g c.p.fuel h false) c v) :
    RWP (afterDelete key g h) (afterDeleteChk key g h) c v := by
  obtain ⟨u, hu⟩ := hA
  exact rwp_afterDelete_of_JA key g h c base hvc hpos KO B hv hk hICEk hsa2 hcap top0 hB u [] v hu hb hmu

/-- The state at a call of `afterDelete` in the stratum's checked copies:
`DelHoleJ` with no fit and no reading. -/
def DelHoleJE (p : Params) (ts : List Tx) (tx : Tx) (top : Top) (v : W) : Prop :=
  DelInvJAE (ctxOf p ts) (viewOf (treeRun p ts)) (kindOracleOf p (treeRun p ts)) tx.base tx.base v ∧
    PutBook (ctxOf p ts) tx.base top v

/-! ## The joint induction with no heights' bound (the first stratum) -/

/-- `HtStartAt` without the heights' bound (`UntakenBound`): the heights' facts at
a state between operations that the joint induction has with no `htb`. -/
def HtStartAt0 (p : Params) (ts : List Tx) (tx : Tx) (w : W) : Prop :=
  ViewHtOK (htOracleOf p (treeRun p ts)) tx.base (ctxOf p ts) ∧
  ViewKlongsWf p (ctxOf p ts).view ∧
  BaseHeights (ctxOf p ts) (htOracleOf p (treeRun p ts)) (viewOf (treeRun p ts)) ∧
  (∀ y h, htOracleOf p (treeRun p ts) y h → h ≤ p.H) ∧
  Book tx.base (ctxOf p ts) w ∧ HtInv (htOracleOf p (treeRun p ts)) tx.base (ctxOf p ts) w ∧
  WriterKlongsWf w

theorem htStart0_of_htStart (p : Params) (ts : List Tx) (tx : Tx) (w : W) (h : HtStartAt p ts tx w) :
    HtStartAt0 p ts tx w := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, _⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

/-- `htStart_of_ht` without `htb` and without the bound. -/
theorem htStart0_of_ht (p : Params) (R : Struct BVal → Time → Prop)
    (hRL : ∀ P t, R P t → RunLinksOK p P t) (hRK : ∀ P t, R P t → KindsAllOK p P)
    (hRH : ∀ P t, R P t → HeightAllOK p P t) (ts : List Tx) (tx : Tx) (hw : Within p (ts ++ [tx]))
    (hr : R (treeRun p ts) ts.length) (z : NodeId) (top : Top)
    (htop : topOf p (ctxOf p ts).view z = .ok top) (pre : List Op) (r : List Bool) (w : W)
    (hpre : (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w))
    (hi : HtInv (htOracleOf p (treeRun p ts)) tx.base (ctxOf p ts) w) :
    HtStartAt0 p ts tx w := by
  have hR := hRL _ _ hr
  have hK := hRK _ _ hr
  have hA := hRH _ _ hr
  have hbk := putBook_reached p ts tx hw hR z top htop pre r w hpre
  have hB := putBase_of_run p ts tx hw hR
  have htimes : StructTimesLE (treeRun p ts) ts.length := treeRun_timesLE p ts
  refine ⟨viewHtOK_of_run p ts tx hw hR hK hA, hB.wf, baseHeights_of p (treeRun p ts) ts.length (ctxOf p ts) rfl
    (by simp [ctxOf]) htimes hR.1 hK hA, ?_, hbk.book, hi, hbk.klongs⟩
  rintro y h ⟨ny, _, _, _, hny⟩
  exact hny ▸ heightOf_le p ny.level

/-- `StartJ` without the heights' bound. -/
def StartJ0 (p : Params) (ts : List Tx) (tx : Tx) (w : W) : Prop :=
  HtStartAt0 p ts tx w ∧ TakeJ2 (ctxOf p ts) (viewOf (treeRun p ts)) tx.base w ∧
    ∀ x o, w.madeFor.lookup x = some o → o < tx.base

/-- `SJ` without the fit and the heights' bound. -/
def SJ0 (p : Params) (ts : List Tx) (tx : Tx) (w : W) : Prop :=
  (TakeS3 p ts tx w ∧ ∀ x o, w.madeFor.lookup x = some o → o < tx.base) ∧ HtStartAt0 p ts tx w ∧
    LiveCountsW p ts w

theorem startJ0_of_startJ (p : Params) (ts : List Tx) (tx : Tx) (w : W) (h : StartJ p ts tx w) :
    StartJ0 p ts tx w :=
  ⟨htStart0_of_htStart p ts tx w h.1, h.2.1, h.2.2⟩

theorem sJ0_of_sJ (p : Params) (ts : List Tx) (tx : Tx) (w : W) (h : SJ p ts tx w) : SJ0 p ts tx w :=
  ⟨⟨h.1.1, h.1.2.2⟩, htStart0_of_htStart p ts tx w h.2.1, h.2.2⟩

/-- A stratum case gives the case with the bound. -/
theorem opCaseOKJ_of_0 (p : Params) (R : Struct BVal → Time → Prop) (Q : List Tx → Op → W → W → Prop)
    (P : Ctx → View BVal → W → Op → Prop) (h : OpCaseOKJS p R (StartJ0 p) Q P) : OpCaseOKJ p R Q P :=
  fun ts tx hw hr z top hz htop pre op post hops r w hpre hSt =>
    h ts tx hw hr z top hz htop pre op post hops r w hpre (startJ0_of_startJ p ts tx w hSt)

theorem opJ2OK_of_0 (p : Params) (R : Struct BVal → Time → Prop) (h : OpJ2OK p R (SJ0 p)) :
    OpJ2OK p R (SJ p) :=
  fun ts tx hw hr z top hz htop pre op post hops r w hpre hT hS =>
    h ts tx hw hr z top hz htop pre op post hops r w hpre hT (sJ0_of_sJ p ts tx w hS)

/-- The first stratum (bergdb 025-05, step 7): the joint induction with no `htb`.
At every state that a transaction's operations reach: `PutInv`, the ranges, the
fill, the heights' walk, the writer's tree and the take-back's node facts, from
the operations' cases whose delete cases take no fit and no heights' bound at
the delete's start (`StartJ0`, `SJ0`), and `hchk` (`OpDelChk2ORJ`, whose
statement has neither). -/
theorem jointHtJ_reached0 (p : Params) (R : Struct BVal → Time → Prop) (hm : p.merges = true)
    (hM : 2 ≤ p.M) (hM4 : 4 ≤ p.M) (hRB : BaseStartOK p R)
    (hRL : ∀ P t, R P t → RunLinksOK p P t) (hRT : ∀ P t, R P t → TreeAt p P t)
    (hRI : ∀ P t, R P t → InvOK p P t) (hRP : ∀ P t, R P t → PointersOK P)
    (hRK : ∀ P t, R P t → KindsAllOK p P) (hRH : ∀ P t, R P t → HeightAllOK p P t)
    (hTp : OpCaseOK p R (QPut (QTree p)) AnyOp) (hPp : OpCaseOK p R (QPut (QPutInv p)) AnyOp)
    (hOp : OpCaseOK p R (QPut (QRange p)) AnyOp)
    (hTd : OpCaseOKJS p R (StartJ0 p) (QTree p) DelMergeCaseL)
    (hPd : OpCaseOKJS p R (StartJ0 p) (QPutInv p) DelMergeCaseL)
    (hOd : OpCaseOKJS p R (StartJ0 p) (QRange p) DelMergeCaseL) (hJ2O : OpJ2OK p R (SJ0 p))
    (hLv : OpCaseOK p R (QLive p) AnyOp) (hchk : OpDelChk2ORJ p R)
    (ts : List Tx) (tx : Tx) (hw : Within p (ts ++ [tx])) (hr : R (treeRun p ts) ts.length)
    (z : NodeId) (top : Top)
    (hz : lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z)
    (htop : topOf p (ctxOf p ts).view z = .ok top) :
    ∀ pre post, tx.ops = pre ++ post → ∀ r w,
      (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
      PutInv (ctxOf p ts) (viewOf (treeRun p ts)) w ∧
      RangeOrder (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey ∧
      LiveCounts p (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey ∧
      HtInv (htOracleOf p (treeRun p ts)) tx.base (ctxOf p ts) w ∧
      WriterTreeOK p (treeRun p ts) (ts.length + 1) w ∧ J2At p (treeRun p ts) (ts.length + 1) tx.base w :=
  jointHtJ_reachedJS p R hm hM hRB hRL hRT hRI hRP hRK hRH (SJ0 p) (StartJ0 p)
    (fun ts tx hw hr z top hz htop pre post hs r w hpre hI hRo hL hH _ =>
      ⟨⟨⟨⟨⟨hI, leafVals_reached p hM ts tx hw top pre post hs r w hpre (hRP _ _ hr) (hRK _ _ hr)⟩,
        base_le_next_reached p hM ts tx hw top pre post hs r w hpre (hRP _ _ hr) (hRK _ _ hr)⟩, hRo⟩,
        stateOK_madeFor p hM4 R hRL ts tx hw hr z top hz htop pre post hs r w hpre⟩,
        htStart0_of_ht p R hRL hRK hRH ts tx hw hr z top htop pre r w hpre hH, hL⟩)
    (fun ts tx hw hr z top hz htop pre post hs r w hpre _ _ _ hH hJ =>
      ⟨htStart0_of_ht p R hRL hRK hRH ts tx hw hr z top htop pre r w hpre hH, hJ,
        stateOK_madeFor p hM4 R hRL ts tx hw hr z top hz htop pre post hs r w hpre⟩)
    hTp hPp hOp hTd hPd hOd hJ2O hLv hchk ts tx hw hr z top hz htop

end SIS.Tree
