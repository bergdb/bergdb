import SIS.Tree.GetCaseBridge
import SIS.Tree.WriterTreeInv

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! The three premises about each operation, assembled over the operation
cases (bergdb 024-12, TP10): the writer's tree (`OpTreeOK`, cost's), `PutInv`
(`OpPutInvOK`, putinv's) and the walk's ranges (`OpRangeOK`, putinv's).

Each is stated per case as `OpCaseOK p R Q P`: from a state between operations
of a transaction within reach that meets `PutInv`, `RangeOrder` and the case P,
the state after the operation meets Q. The three posts are `QTree`, `QPutInv`
and `QRange`. Over the nine cases (`opCase_cover`) a post holds for every
operation (`opCaseOK_of_cases`). The three together hold at every state
between operations (`joint_reached`), so they give the three premises in the
forms that `getOK_scanOK_of_open` takes; `OpTreeOK`, which has no premise on
the run, for runs that all meet R (`opTreeOK_of_any`).

`getOK_scanOK_of_cases` gives TP10 and TP11 from the cases;
`getOK_scanOK_of_cases_merges` for the parameters of `MergeParamsOK`, where
the merges are on and the cases (5) to (9) are void. -/

/-! ## A post per case -/

/-- An operation case P with post Q: from a state between operations of a
transaction within reach that meets `PutInv`, `RangeOrder` and P, the state
after the operation meets Q. -/
def OpCaseOK (p : Params) (R : Struct BVal → Time → Prop) (Q : List Tx → Op → W → W → Prop)
    (P : Ctx → View BVal → W → Op → Prop) : Prop :=
  ∀ ts tx, Within p (ts ++ [tx]) → R (treeRun p ts) ts.length → ∀ z top,
    lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z →
    topOf p (ctxOf p ts).view z = .ok top →
    ∀ pre op post, tx.ops = pre ++ op :: post →
    ∀ r w, (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
    PutInv (ctxOf p ts) (viewOf (treeRun p ts)) w →
    RangeOrder (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey →
    P (ctxOf p ts) (viewOf (treeRun p ts)) w op →
    WriterWP (putKv op) (ctxOf p ts) w (fun _ w' => Q ts op w w')

/-- Every operation. -/
def AnyOp : Ctx → View BVal → W → Op → Prop := fun _ _ _ _ => True

/-- The writer's tree after the operation. -/
def QTree (p : Params) : List Tx → Op → W → W → Prop :=
  fun ts _ _ w' => WriterTreeOK p (treeRun p ts) (ts.length + 1) w'

/-- `PutInv` after the operation, the writer's tree after it given. -/
def QPutInv (p : Params) : List Tx → Op → W → W → Prop :=
  fun ts _ _ w' => WriterTreeOK p (treeRun p ts) (ts.length + 1) w' →
    PutInv (ctxOf p ts) (viewOf (treeRun p ts)) w'

/-- The walk's ranges after the operation, the writer's tree after it given. -/
def QRange (p : Params) : List Tx → Op → W → W → Prop :=
  fun ts _ _ w' => WriterTreeOK p (treeRun p ts) (ts.length + 1) w' →
    RangeOrder (wNode p (viewOf (treeRun p ts)) w') (ts.length + 1) w'.top.rootKey

/-- Over the nine cases, a post holds for every operation. -/
theorem opCaseOK_of_cases (p : Params) (R : Struct BVal → Time → Prop)
    (Q : List Tx → Op → W → W → Prop)
    (c1 : OpCaseOK p R Q PutLeafRoomCase) (c2 : OpCaseOK p R Q PutLeafFullCase)
    (c3 : OpCaseOK p R Q PutNewSegCase) (c4 : OpCaseOK p R Q DelMergeCase)
    (c5 : OpCaseOK p R Q DelNoLeafCase) (c6 : OpCaseOK p R Q DelNoopCase)
    (c7 : OpCaseOK p R Q DelEmptyCase) (c8 : OpCaseOK p R Q DelRoomCase)
    (c9 : OpCaseOK p R Q DelFullCase) :
    OpCaseOK p R Q AnyOp := by
  intro ts tx hw hr z top hz htop pre op post hsplit r w hpre hI hRO _
  have hcase : ∀ P : Ctx → View BVal → W → Op → Prop, OpCaseOK p R Q P →
      P (ctxOf p ts) (viewOf (treeRun p ts)) w op →
      WriterWP (putKv op) (ctxOf p ts) w (fun _ w' => Q ts op w w') :=
    fun P hc hPc => hc ts tx hw hr z top hz htop pre op post hsplit r w hpre hI hRO hPc
  rcases opCase_cover (ctxOf p ts) (viewOf (treeRun p ts)) w op with
    h | h | h | h | h | h | h | h | h
  · exact hcase _ c1 h
  · exact hcase _ c2 h
  · exact hcase _ c3 h
  · exact hcase _ c4 h
  · exact hcase _ c5 h
  · exact hcase _ c6 h
  · exact hcase _ c7 h
  · exact hcase _ c8 h
  · exact hcase _ c9 h

/-- A case that needs the merges off is void with them on. -/
theorem opCaseOK_void (p : Params) (R : Struct BVal → Time → Prop)
    (Q : List Tx → Op → W → W → Prop) (P : Ctx → View BVal → W → Op → Prop)
    (hm : p.merges = true) (hP : ∀ c base w op, P c base w op → c.p.merges = false) :
    OpCaseOK p R Q P := by
  intro ts _ _ _ _ _ _ _ _ op _ _ _ w _ _ _ hPc
  have h : p.merges = false := hP _ _ _ _ hPc
  rw [hm] at h
  cases h

theorem delNoLeafCase_merges (c : Ctx) (base : View BVal) (w : W) (op : Op)
    (h : DelNoLeafCase c base w op) : c.p.merges = false :=
  let ⟨_, _, hm, _⟩ := h; hm

theorem delNoopCase_merges (c : Ctx) (base : View BVal) (w : W) (op : Op)
    (h : DelNoopCase c base w op) : c.p.merges = false :=
  let ⟨_, _, _, _, _, hm, _⟩ := h; hm

theorem delEmptyCase_merges (c : Ctx) (base : View BVal) (w : W) (op : Op)
    (h : DelEmptyCase c base w op) : c.p.merges = false :=
  let ⟨_, _, _, _, _, hm, _⟩ := h; hm

theorem delRoomCase_merges (c : Ctx) (base : View BVal) (w : W) (op : Op)
    (h : DelRoomCase c base w op) : c.p.merges = false :=
  let ⟨_, _, _, _, _, hm, _⟩ := h; hm

theorem delFullCase_merges (c : Ctx) (base : View BVal) (w : W) (op : Op)
    (h : DelFullCase c base w op) : c.p.merges = false :=
  let ⟨_, _, _, _, _, hm, _⟩ := h; hm

/-- Over the cases (1) to (4), with the merges on, a post holds for every
operation: the cases (5) to (9) are void. -/
theorem opCaseOK_of_cases_merges (p : Params) (R : Struct BVal → Time → Prop)
    (Q : List Tx → Op → W → W → Prop) (hm : p.merges = true)
    (c1 : OpCaseOK p R Q PutLeafRoomCase) (c2 : OpCaseOK p R Q PutLeafFullCase)
    (c3 : OpCaseOK p R Q PutNewSegCase) (c4 : OpCaseOK p R Q DelMergeCase) :
    OpCaseOK p R Q AnyOp :=
  opCaseOK_of_cases p R Q c1 c2 c3 c4 (opCaseOK_void p R Q _ hm delNoLeafCase_merges)
    (opCaseOK_void p R Q _ hm delNoopCase_merges) (opCaseOK_void p R Q _ hm delEmptyCase_merges)
    (opCaseOK_void p R Q _ hm delRoomCase_merges) (opCaseOK_void p R Q _ hm delFullCase_merges)

/-! ## The three together along a transaction -/

/-- `PutInv` and the walk's ranges (and with `PutInv` the writer's tree) at
every state that a prefix of a transaction's operations reaches: from its
first state (`putInv_init`, `rangeOrder_init`) and the three posts at every
operation. -/
theorem joint_reached (p : Params) (R : Struct BVal → Time → Prop)
    (hRL : ∀ P t, R P t → RunLinksOK p P t)
    (hT : OpCaseOK p R (QTree p) AnyOp) (hP : OpCaseOK p R (QPutInv p) AnyOp)
    (hO : OpCaseOK p R (QRange p) AnyOp)
    (ts : List Tx) (tx : Tx) (hw : Within p (ts ++ [tx])) (hr : R (treeRun p ts) ts.length)
    (hTA : TreeAt p (treeRun p ts) ts.length) (hI : InvOK p (treeRun p ts) ts.length)
    (z : NodeId) (top : Top)
    (hz : lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z)
    (htop : topOf p (ctxOf p ts).view z = .ok top) :
    ∀ pre post, tx.ops = pre ++ post → ∀ r w,
      (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
      PutInv (ctxOf p ts) (viewOf (treeRun p ts)) w ∧
      RangeOrder (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey := by
  intro pre
  suffices hk : ∀ k, ∀ pre : List Op, pre.length = k → ∀ post, tx.ops = pre ++ post → ∀ r w,
      (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
      PutInv (ctxOf p ts) (viewOf (treeRun p ts)) w ∧
      RangeOrder (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey
    from hk pre.length pre rfl
  intro k
  induction k with
  | zero =>
    intro pre hl _ _ r w h
    have hnil : pre = [] := List.eq_nil_of_length_eq_zero hl
    subst hnil
    simp only [List.mapM_nil, pure, ReaderT.pure, StateT.pure, Except.pure, Except.ok.injEq,
      Prod.mk.injEq] at h
    rw [← h.2]
    exact ⟨putInv_init p ts tx hw (hRL _ _ hr) hTA hI z top hz htop,
      rangeOrder_init p ts tx hI z top hz htop⟩
  | succ k ih =>
    intro pre hl post hsplit r w h
    rcases List.eq_nil_or_concat pre with hnil | ⟨pre', op, hpre⟩
    · subst hnil; simp at hl
    · rw [List.concat_eq_append] at hpre
      subst hpre
      have hl' : pre'.length = k := by simp at hl; omega
      rw [List.mapM_append] at h
      simp only [List.mapM_cons, List.mapM_nil, bind, ReaderT.bind, StateT.bind, Except.bind] at h
      cases h1 : (pre'.mapM putKv) (ctxOf p ts) (wInit tx top) with
      | error e => rw [h1] at h; cases h
      | ok rw1 =>
        rcases rw1 with ⟨r1, w1⟩
        rw [h1] at h
        simp only at h
        cases h2 : putKv op (ctxOf p ts) w1 with
        | error e => rw [h2] at h; cases h
        | ok aw =>
          rcases aw with ⟨a, w2⟩
          rw [h2] at h
          simp only [pure, ReaderT.pure, StateT.pure, Except.pure, Except.ok.injEq,
            Prod.mk.injEq] at h
          have hsplit' : tx.ops = pre' ++ op :: post := by rw [hsplit]; simp
          obtain ⟨hI1, hR1⟩ := ih pre' hl' (op :: post) hsplit' r1 w1 h1
          have hT2 : WriterTreeOK p (treeRun p ts) (ts.length + 1) w2 :=
            hT ts tx hw hr z top hz htop pre' op post hsplit' r1 w1 h1 hI1 hR1 trivial a w2 h2
          have hI2 := hP ts tx hw hr z top hz htop pre' op post hsplit' r1 w1 h1 hI1 hR1 trivial a w2
            h2 hT2
          have hR2 := hO ts tx hw hr z top hz htop pre' op post hsplit' r1 w1 h1 hI1 hR1 trivial a w2
            h2 hT2
          rw [← h.2]
          exact ⟨hI2, hR2⟩

/-! ## The three premises in the forms the assembly takes -/

theorem opRangeOK_of_any (p : Params) (R : Struct BVal → Time → Prop)
    (hO : OpCaseOK p R (QRange p) AnyOp) : OpRangeOK p R := by
  intro ts tx hw hr z top hz htop pre op post hsplit r w hpre hI hRO
  exact hO ts tx hw hr z top hz htop pre op post hsplit r w hpre hI hRO trivial

theorem opPutInvOK_of_any (p : Params) (R : Struct BVal → Time → Prop)
    (hRL : ∀ P t, R P t → RunLinksOK p P t) (hRT : ∀ P t, R P t → TreeAt p P t)
    (hRI : ∀ P t, R P t → InvOK p P t)
    (hT : OpCaseOK p R (QTree p) AnyOp) (hP : OpCaseOK p R (QPutInv p) AnyOp)
    (hO : OpCaseOK p R (QRange p) AnyOp) : OpPutInvOK p R := by
  intro ts tx hw hr z top hz htop pre op post hsplit r w hpre hI
  have hRO := (joint_reached p R hRL hT hP hO ts tx hw hr (hRT _ _ hr) (hRI _ _ hr) z top hz htop
    pre (op :: post) hsplit r w hpre).2
  exact hP ts tx hw hr z top hz htop pre op post hsplit r w hpre hI hRO trivial

theorem opTreeInvOK_of_any (p : Params) (R : Struct BVal → Time → Prop)
    (hRL : ∀ P t, R P t → RunLinksOK p P t) (hRT : ∀ P t, R P t → TreeAt p P t)
    (hRI : ∀ P t, R P t → InvOK p P t)
    (hT : OpCaseOK p R (QTree p) AnyOp) (hP : OpCaseOK p R (QPutInv p) AnyOp)
    (hO : OpCaseOK p R (QRange p) AnyOp) : OpTreeInvOK p R := by
  intro ts tx hw hr z top hz htop pre op post hsplit r w hpre hI
  have hRO := (joint_reached p R hRL hT hP hO ts tx hw hr (hRT _ _ hr) (hRI _ _ hr) z top hz htop
    pre (op :: post) hsplit r w hpre).2
  exact hT ts tx hw hr z top hz htop pre op post hsplit r w hpre hI hRO trivial

/-- `OpTreeOK`, which has no premise on the run, when every run within reach
meets R. -/
theorem opTreeOK_of_any (p : Params) (R : Struct BVal → Time → Prop)
    (hR : ∀ ts, Within p ts → R (treeRun p ts) ts.length)
    (hRL : ∀ P t, R P t → RunLinksOK p P t) (hRT : ∀ P t, R P t → TreeAt p P t)
    (hRI : ∀ P t, R P t → InvOK p P t)
    (hT : OpCaseOK p R (QTree p) AnyOp) (hP : OpCaseOK p R (QPutInv p) AnyOp)
    (hO : OpCaseOK p R (QRange p) AnyOp) : OpTreeOK p := by
  intro ts tx hw z top hz htop pre op post hsplit r w hpre _
  have hr := hR ts (within_snoc_prefix p ts tx hw)
  obtain ⟨hI, hRO⟩ := joint_reached p R hRL hT hP hO ts tx hw hr (hRT _ _ hr) (hRI _ _ hr) z top
    hz htop pre (op :: post) hsplit r w hpre
  exact hT ts tx hw hr z top hz htop pre op post hsplit r w hpre hI hRO trivial

/-! ## TP10 and TP11 from the cases -/

/-- TP10 and TP11 from TP7, the run's links and P's tree at every run within
reach, the fuel premise along transactions, and the cases: the writer's tree,
`PutInv` and the walk's ranges of each of the nine, and the reading of (4),
(7) and (9) (the other six are proved, `GetCaseBridge.lean`), for a node size
and a split threshold of 2 or more. -/
theorem getOK_scanOK_of_cases (p : Params) (hM : 2 ≤ p.M) (hsa : 2 ≤ p.splitAbove)
    (hinv : InvPreserved p)
    (hlinks : ∀ ts, Within p ts → RunLinksOK p (treeRun p ts) ts.length)
    (htree : ∀ ts, Within p ts → TreeAt p (treeRun p ts) ts.length)
    (hfit : TxSegFitsOK p (RunOK p))
    (t1 : OpCaseOK p (RunOK p) (QTree p) PutLeafRoomCase)
    (t2 : OpCaseOK p (RunOK p) (QTree p) PutLeafFullCase)
    (t3 : OpCaseOK p (RunOK p) (QTree p) PutNewSegCase)
    (t4 : OpCaseOK p (RunOK p) (QTree p) DelMergeCase)
    (t5 : OpCaseOK p (RunOK p) (QTree p) DelNoLeafCase)
    (t6 : OpCaseOK p (RunOK p) (QTree p) DelNoopCase)
    (t7 : OpCaseOK p (RunOK p) (QTree p) DelEmptyCase)
    (t8 : OpCaseOK p (RunOK p) (QTree p) DelRoomCase)
    (t9 : OpCaseOK p (RunOK p) (QTree p) DelFullCase)
    (i1 : OpCaseOK p (RunOK p) (QPutInv p) PutLeafRoomCase)
    (i2 : OpCaseOK p (RunOK p) (QPutInv p) PutLeafFullCase)
    (i3 : OpCaseOK p (RunOK p) (QPutInv p) PutNewSegCase)
    (i4 : OpCaseOK p (RunOK p) (QPutInv p) DelMergeCase)
    (i5 : OpCaseOK p (RunOK p) (QPutInv p) DelNoLeafCase)
    (i6 : OpCaseOK p (RunOK p) (QPutInv p) DelNoopCase)
    (i7 : OpCaseOK p (RunOK p) (QPutInv p) DelEmptyCase)
    (i8 : OpCaseOK p (RunOK p) (QPutInv p) DelRoomCase)
    (i9 : OpCaseOK p (RunOK p) (QPutInv p) DelFullCase)
    (r1 : OpCaseOK p (RunOK p) (QRange p) PutLeafRoomCase)
    (r2 : OpCaseOK p (RunOK p) (QRange p) PutLeafFullCase)
    (r3 : OpCaseOK p (RunOK p) (QRange p) PutNewSegCase)
    (r4 : OpCaseOK p (RunOK p) (QRange p) DelMergeCase)
    (r5 : OpCaseOK p (RunOK p) (QRange p) DelNoLeafCase)
    (r6 : OpCaseOK p (RunOK p) (QRange p) DelNoopCase)
    (r7 : OpCaseOK p (RunOK p) (QRange p) DelEmptyCase)
    (r8 : OpCaseOK p (RunOK p) (QRange p) DelRoomCase)
    (r9 : OpCaseOK p (RunOK p) (QRange p) DelFullCase)
    (c4 : OpGetCaseOK p (RunOK p) DelMergeCase) (c7 : OpGetCaseOK p (RunOK p) DelEmptyCase)
    (c9 : OpGetCaseOK p (RunOK p) DelFullCase) :
    GetOK p ∧ ScanOK p := by
  have hR : ∀ ts, Within p ts → RunOK p (treeRun p ts) ts.length :=
    fun ts hw => ⟨hlinks ts hw, htree ts hw, (hinv ts hw ts.length (Nat.le_refl _)).1⟩
  have hT := opCaseOK_of_cases p _ _ t1 t2 t3 t4 t5 t6 t7 t8 t9
  have hP := opCaseOK_of_cases p _ _ i1 i2 i3 i4 i5 i6 i7 i8 i9
  have hO := opCaseOK_of_cases p _ _ r1 r2 r3 r4 r5 r6 r7 r8 r9
  have hRL : ∀ P t, RunOK p P t → RunLinksOK p P t := fun _ _ h => h.1
  have hRT : ∀ P t, RunOK p P t → TreeAt p P t := fun _ _ h => h.2.1
  have hRI : ∀ P t, RunOK p P t → InvOK p P t := fun _ _ h => h.2.2
  exact getOK_scanOK_of_open_cases p hM hsa hinv hlinks htree
    (opTreeOK_of_any p _ hR hRL hRT hRI hT hP hO) (opPutInvOK_of_any p _ hRL hRT hRI hT hP hO)
    (opRangeOK_of_any p _ hO) hfit c4 c7 c9

/-- `getOK_scanOK_of_cases` for the parameters of `MergeParamsOK`: the merges
are on, the cases (5) to (9) are void, and of the cases are left the writer's
tree, `PutInv` and the walk's ranges of (1) to (4), and the reading of (4). -/
theorem getOK_scanOK_of_cases_merges (p : Params) (hp : MergeParamsOK p) (hinv : InvPreserved p)
    (hlinks : ∀ ts, Within p ts → RunLinksOK p (treeRun p ts) ts.length)
    (htree : ∀ ts, Within p ts → TreeAt p (treeRun p ts) ts.length)
    (hfit : TxSegFitsOK p (RunOK p))
    (t1 : OpCaseOK p (RunOK p) (QTree p) PutLeafRoomCase)
    (t2 : OpCaseOK p (RunOK p) (QTree p) PutLeafFullCase)
    (t3 : OpCaseOK p (RunOK p) (QTree p) PutNewSegCase)
    (t4 : OpCaseOK p (RunOK p) (QTree p) DelMergeCase)
    (i1 : OpCaseOK p (RunOK p) (QPutInv p) PutLeafRoomCase)
    (i2 : OpCaseOK p (RunOK p) (QPutInv p) PutLeafFullCase)
    (i3 : OpCaseOK p (RunOK p) (QPutInv p) PutNewSegCase)
    (i4 : OpCaseOK p (RunOK p) (QPutInv p) DelMergeCase)
    (r1 : OpCaseOK p (RunOK p) (QRange p) PutLeafRoomCase)
    (r2 : OpCaseOK p (RunOK p) (QRange p) PutLeafFullCase)
    (r3 : OpCaseOK p (RunOK p) (QRange p) PutNewSegCase)
    (r4 : OpCaseOK p (RunOK p) (QRange p) DelMergeCase)
    (c4 : OpGetCaseOK p (RunOK p) DelMergeCase) :
    GetOK p ∧ ScanOK p := by
  have hm : p.merges = true := by
    unfold MergeParamsOK at hp; unfold Params.merges; simp only [decide_eq_true_eq]; omega
  have hR : ∀ ts, Within p ts → RunOK p (treeRun p ts) ts.length :=
    fun ts hw => ⟨hlinks ts hw, htree ts hw, (hinv ts hw ts.length (Nat.le_refl _)).1⟩
  have hT := opCaseOK_of_cases_merges p _ _ hm t1 t2 t3 t4
  have hP := opCaseOK_of_cases_merges p _ _ hm i1 i2 i3 i4
  have hO := opCaseOK_of_cases_merges p _ _ hm r1 r2 r3 r4
  have hRL : ∀ P t, RunOK p P t → RunLinksOK p P t := fun _ _ h => h.1
  have hRT : ∀ P t, RunOK p P t → TreeAt p P t := fun _ _ h => h.2.1
  have hRI : ∀ P t, RunOK p P t → InvOK p P t := fun _ _ h => h.2.2
  exact getOK_scanOK_of_open_merges p hp hinv hlinks htree
    (opTreeOK_of_any p _ hR hRL hRT hRI hT hP hO) (opPutInvOK_of_any p _ hRL hRT hRI hT hP hO)
    (opRangeOK_of_any p _ hO) hfit c4

end SIS.Tree
