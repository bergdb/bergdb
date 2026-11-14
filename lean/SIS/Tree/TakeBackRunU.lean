/-
The take-back's joint induction with the writer's tree under a run premise
(bergdb 024-12, TP4 and TP7): `OpTreeOKUnder p R`, cost's `OpTreeOK` for runs
that meet R, the form latest's assembly gives from its operation cases
(`GetOpAssembly.lean`). Each theorem here is the one of the same name without
`U` (TakeBackRun.lean, TakeBackRunT.lean, TakeBackDead.lean, WriterTree.lean)
with `OpTreeOKUnder` in place of `OpTreeOK`.
-/
import SIS.Tree.TakeBackDead

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- cost's `OpTreeOK` for the runs that meet R: every operation of a
transaction within reach, from a state with the writer's tree that its earlier
operations reach, keeps the writer's tree. -/
def OpTreeOKUnder (p : Params) (R : Struct BVal → Time → Prop) : Prop :=
  ∀ ts tx, Within p (ts ++ [tx]) → R (treeRun p ts) ts.length → ∀ z top,
    lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z →
    topOf p (ctxOf p ts).view z = .ok top →
    ∀ pre op post, tx.ops = pre ++ op :: post →
    ∀ r w, (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
    WriterTreeOK p (treeRun p ts) (ts.length + 1) w →
    WriterWP (putKv op) (ctxOf p ts) w (fun _ w' =>
      WriterTreeOK p (treeRun p ts) (ts.length + 1) w')

/-- Every state that a prefix of the operations reaches has the writer's tree,
from the first state's and `OpTreeOK`. -/
theorem writerTreeOK_foldU (p : Params) (R : Struct BVal → Time → Prop) (ho : OpTreeOKUnder p R)
    (ts : List Tx) (tx : Tx) (hw : Within p (ts ++ [tx])) (hr : R (treeRun p ts) ts.length) (z : NodeId) (top : Top)
    (hz : lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z)
    (htop : topOf p (ctxOf p ts).view z = .ok top) :
    ∀ todo done extra, tx.ops = done ++ todo ++ extra → ∀ r w,
      (done.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
      WriterTreeOK p (treeRun p ts) (ts.length + 1) w →
      ∀ r' w', (todo.mapM putKv) (ctxOf p ts) w = .ok (r', w') →
      WriterTreeOK p (treeRun p ts) (ts.length + 1) w' := by
  intro todo
  induction todo with
  | nil =>
    intro done _ _ r w _ hT r' w' hrun
    simp only [List.mapM_nil, pure, ReaderT.pure, StateT.pure, Except.pure, Except.ok.injEq,
      Prod.mk.injEq] at hrun
    rw [← hrun.2]
    exact hT
  | cons op rest ih =>
    intro done extra hsplit r w hdone hT r' w' hrun
    obtain ⟨a, w1, r1, h1, h2⟩ := mapM_cons_run op rest _ w w' r' hrun
    have hT1 := ho ts tx hw hr z top hz htop done op (rest ++ extra) (by rw [hsplit]; simp) r w hdone
      hT a w1 h1
    have hdone' := mapM_snoc_run done op _ _ w w1 r a hdone h1
    exact ih (done ++ [op]) extra (by rw [hsplit]; simp) _ w1 hdone' hT1 r1 w' h2

/-- The writer's tree at every state between operations, from P's tree before
the transaction and `OpTreeOK`. -/
theorem writerTreeOK_reachedU (p : Params) (R : Struct BVal → Time → Prop) (ho : OpTreeOKUnder p R)
    (ts : List Tx) (tx : Tx) (hw : Within p (ts ++ [tx])) (hr : R (treeRun p ts) ts.length) (z : NodeId) (top : Top)
    (hz : lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z)
    (htop : topOf p (ctxOf p ts).view z = .ok top)
    (hT : TreeAt p (treeRun p ts) ts.length) (pre : List Tree.Op) (post : List Tree.Op)
    (hsplit : tx.ops = pre ++ post) (r : List Bool) (w : W)
    (hpre : (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w)) :
    WriterTreeOK p (treeRun p ts) (ts.length + 1) w :=
  writerTreeOK_foldU p R ho ts tx hw hr z top hz htop pre [] post (by simp [hsplit]) [] (wInit tx top)
    (by simp only [List.mapM_nil, pure, ReaderT.pure, StateT.pure, Except.pure])
    (writerTreeOK_init p ts tx z top hz htop hT) r w hpre

/-- P's tree after one transaction, from P's tree before it, `OpTreeOK` and the
lift of that transaction. -/
theorem treeAt_stepU (p : Params) (R : Struct BVal → Time → Prop) (ho : OpTreeOKUnder p R)
    (ts : List Tx) (tx : Tx) (hw : Within p (ts ++ [tx])) (hr : R (treeRun p ts) ts.length) (hT : TreeAt p (treeRun p ts) ts.length)
    (hl : CommitLiftAt p ts tx) : TreeAt p (treeRun p (ts ++ [tx])) (ts.length + 1) := by
  obtain ⟨noops, w, hrun⟩ := within_last_ok p ts tx hw
  obtain ⟨z, top, hz, htop, hops⟩ := runOps_ok p _ _ _ _ noops w hrun
  have hW := writerTreeOK_reachedU p R ho ts tx hw hr z top hz htop hT tx.ops [] (by simp) noops w hops
  obtain ⟨hK, htaken, htopt⟩ := hl noops w hrun
  have hR := rootAt_commit_of_lift p ts tx hw noops w hrun hK htaken htopt
  exact ⟨w.top.rootKey, hR, treeOK_congr_look _ _ _ _ (funext hK).symm hW⟩

end SIS.Tree
