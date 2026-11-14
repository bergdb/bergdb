/-
TP7's live counts at an operation's start, carried with `PutInv` and the walk's
ranges along a transaction (bergdb 024-12). A case of the delete with the
merges may need `LiveCounts` of the state it starts from: with it, the upward
delete's stop node is a segment leaf, so LE-b never runs (cost's
`stopLeaf_of_liveCounts`). Such a case is stated with `LiveCounts` in its case
predicate; the joint induction here supplies it at every state that a prefix of
a transaction's operations reaches (`jointLive_reached`), and so gives the
cases at every state (`opCaseOK_any_of_L`) and `LiveCounts` there
(`liveStateOK_of_L`).
-/
import SIS.Tree.LiveCounts
import SIS.Tree.TakeBackRunJ

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- Every operation, from a state with TP7's live counts. -/
def AnyOpL : Ctx → View BVal → W → Op → Prop :=
  fun c base w _ => LiveCounts c.p (wNode c.p base w) c.i w.top.rootKey

/-- A case at every operation holds at every operation from a state with the
live counts. -/
theorem opCaseOK_L_of_any (p : Params) (R : Struct BVal → Time → Prop)
    (Q : List Tx → Op → W → W → Prop) (h : OpCaseOK p R Q AnyOp) : OpCaseOK p R Q AnyOpL :=
  fun ts tx hw hr z top hz htop pre op post hs r w hpre hI hRO _ =>
    h ts tx hw hr z top hz htop pre op post hs r w hpre hI hRO trivial

/-- `PutInv`, the walk's ranges and the live counts at every state that a
prefix of a transaction's operations reaches, from the cases at every operation
from a state with the live counts. -/
theorem jointLive_reached (p : Params) (R : Struct BVal → Time → Prop)
    (hRL : ∀ P t, R P t → RunLinksOK p P t)
    (hT : OpCaseOK p R (QTree p) AnyOpL) (hP : OpCaseOK p R (QPutInv p) AnyOpL)
    (hO : OpCaseOK p R (QRange p) AnyOpL) (hLv : OpCaseOK p R (QLive p) AnyOpL)
    (ts : List Tx) (tx : Tx) (hw : Within p (ts ++ [tx])) (hr : R (treeRun p ts) ts.length)
    (hTA : TreeAt p (treeRun p ts) ts.length) (hI : InvOK p (treeRun p ts) ts.length)
    (z : NodeId) (top : Top)
    (hz : lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z)
    (htop : topOf p (ctxOf p ts).view z = .ok top) :
    ∀ pre post, tx.ops = pre ++ post → ∀ r w,
      (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
      PutInv (ctxOf p ts) (viewOf (treeRun p ts)) w ∧
      RangeOrder (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey ∧
      LiveCounts p (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey := by
  intro pre
  suffices hk : ∀ k, ∀ pre : List Op, pre.length = k → ∀ post, tx.ops = pre ++ post → ∀ r w,
      (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
      PutInv (ctxOf p ts) (viewOf (treeRun p ts)) w ∧
      RangeOrder (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey ∧
      LiveCounts p (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey
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
      rangeOrder_init p ts tx hI z top hz htop, liveCounts_init p ts tx hI z top hz htop⟩
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
          obtain ⟨hI1, hR1, hL1⟩ := ih pre' hl' (op :: post) hsplit' r1 w1 h1
          have hT2 : WriterTreeOK p (treeRun p ts) (ts.length + 1) w2 :=
            hT ts tx hw hr z top hz htop pre' op post hsplit' r1 w1 h1 hI1 hR1 hL1 a w2 h2
          have hI2 := hP ts tx hw hr z top hz htop pre' op post hsplit' r1 w1 h1 hI1 hR1 hL1 a w2
            h2 hT2
          have hR2 := hO ts tx hw hr z top hz htop pre' op post hsplit' r1 w1 h1 hI1 hR1 hL1 a w2
            h2 hT2
          have hL2 := hLv ts tx hw hr z top hz htop pre' op post hsplit' r1 w1 h1 hI1 hR1 hL1 a w2
            h2 hT2 hL1
          rw [← h.2]
          exact ⟨hI2, hR2, hL2⟩

/-- The cases at every operation, from the cases at every operation from a
state with the live counts, which every state a transaction reaches has. -/
theorem opCaseOK_any_of_L (p : Params) (R : Struct BVal → Time → Prop)
    (hRL : ∀ P t, R P t → RunLinksOK p P t) (hRT : ∀ P t, R P t → TreeAt p P t)
    (hRI : ∀ P t, R P t → InvOK p P t)
    (hT : OpCaseOK p R (QTree p) AnyOpL) (hP : OpCaseOK p R (QPutInv p) AnyOpL)
    (hO : OpCaseOK p R (QRange p) AnyOpL) (hLv : OpCaseOK p R (QLive p) AnyOpL)
    (Q : List Tx → Op → W → W → Prop) (hQ : OpCaseOK p R Q AnyOpL) : OpCaseOK p R Q AnyOp := by
  intro ts tx hw hr z top hz htop pre op post hsplit r w hpre hI hRO _
  have hL := (jointLive_reached p R hRL hT hP hO hLv ts tx hw hr (hRT _ _ hr) (hRI _ _ hr) z top hz
    htop pre (op :: post) hsplit r w hpre).2.2
  exact hQ ts tx hw hr z top hz htop pre op post hsplit r w hpre hI hRO hL

/-- The live counts at every state between operations. -/
theorem liveStateOK_of_L (p : Params) (R : Struct BVal → Time → Prop)
    (hRL : ∀ P t, R P t → RunLinksOK p P t) (hRT : ∀ P t, R P t → TreeAt p P t)
    (hRI : ∀ P t, R P t → InvOK p P t)
    (hT : OpCaseOK p R (QTree p) AnyOpL) (hP : OpCaseOK p R (QPutInv p) AnyOpL)
    (hO : OpCaseOK p R (QRange p) AnyOpL) (hLv : OpCaseOK p R (QLive p) AnyOpL) :
    StateOK p R (fun ts _ w => LiveCounts p (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1)
      w.top.rootKey) :=
  fun ts tx hw hr z top hz htop pre post hsplit r w hpre =>
    (jointLive_reached p R hRL hT hP hO hLv ts tx hw hr (hRT _ _ hr) (hRI _ _ hr) z top hz htop pre
      post hsplit r w hpre).2.2

/-- The cases of every operation from a state with the live counts, with the
delete with the merges (4) given from such a state: the put cases (1) to (3)
need no live counts. -/
theorem opCaseOK_of_cases_mergesL (p : Params) (R : Struct BVal → Time → Prop)
    (Q : List Tx → Op → W → W → Prop) (hm : p.merges = true)
    (c1 : OpCaseOK p R Q PutLeafRoomCase) (c2 : OpCaseOK p R Q PutLeafFullCase)
    (c3 : OpCaseOK p R Q PutNewSegCase)
    (c4 : OpCaseOK p R Q (fun c base w op =>
      DelMergeCase c base w op ∧ LiveCounts c.p (wNode c.p base w) c.i w.top.rootKey)) :
    OpCaseOK p R Q AnyOpL := by
  let Q' : List Tx → Op → W → W → Prop := fun ts op w w' =>
    LiveCounts p (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey → Q ts op w w'
  have lift : ∀ C, OpCaseOK p R Q C → OpCaseOK p R Q' C :=
    fun C h ts tx hw hr z top hz htop pre op post hs r w hpre hI hRO hC =>
      writerWP_mono (h ts tx hw hr z top hz htop pre op post hs r w hpre hI hRO hC)
        (fun _ _ hq _ => hq)
  have c4' : OpCaseOK p R Q' DelMergeCase := by
    intro ts tx hw hr z top hz htop pre op post hs r w hpre hI hRO hC
    by_cases hL : LiveCounts p (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey
    · exact writerWP_mono (c4 ts tx hw hr z top hz htop pre op post hs r w hpre hI hRO ⟨hC, hL⟩)
        (fun _ _ hq _ => hq)
    · intro _ _ _ hL'
      exact absurd hL' hL
  have hall := opCaseOK_of_cases_merges p R Q' hm (lift _ c1) (lift _ c2) (lift _ c3) c4'
  intro ts tx hw hr z top hz htop pre op post hs r w hpre hI hRO hL
  exact writerWP_mono (hall ts tx hw hr z top hz htop pre op post hs r w hpre hI hRO trivial)
    (fun _ _ hq => hq hL)

/-- A case at every operation holds in every narrower case. -/
theorem opCaseOK_of_any (p : Params) (R : Struct BVal → Time → Prop)
    (Q : List Tx → Op → W → W → Prop) (C : Ctx → View BVal → W → Op → Prop)
    (h : OpCaseOK p R Q AnyOp) : OpCaseOK p R Q C :=
  fun ts tx hw hr z top hz htop pre op post hs r w hpre hI hRO _ =>
    h ts tx hw hr z top hz htop pre op post hs r w hpre hI hRO trivial

end SIS.Tree
