import SIS.Tree.GetLatest
import SIS.Tree.WriterWP
import SIS.Tree.MergeProps
import SIS.Tree.MergeOpBoundProof

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! TP10's step for one transaction (`TxGetOK`, bergdb 024-12) from three
statements about the writer: the writer's state before the first operation
reads as P at the time before (`InitGetOK`), each operation changes what the
writer's state reads by that operation alone (`OpGetOK`), and the structure
after the transaction reads as the writer's last state (`CommitGetOK`). The
reading through a writer's state is `wGet`: its own nodes and values first,
then P@(i-1). -/

/-! ## A get through any node reader -/

/-- `getEq` with the key nodes given by a function. -/
def getEqR (nodeOf : NodeId → Option KNode) (t : Time) (cv : Nat) : Nat → NodeId → Option NodeId
  | 0, _ => none
  | f + 1, x =>
    match nodeOf x with
    | none => none
    | some n =>
      if n.leaf then (n.searchEq t cv).map (·.y)
      else
        match n.searchLte t cv with
        | none => none
        | some fd => getEqR nodeOf t cv f fd.y

/-- `getFrom` with the key nodes and the values given by functions. -/
def getFromR (nodeOf : NodeId → Option KNode) (valOf : NodeId → Option Nat) (t : Time)
    (fuel : Nat) : List Nat → NodeId → Option Nat
  | [], _ => none
  | [cv], r => (getEqR nodeOf t cv fuel r).bind valOf
  | cv :: rest, r =>
    match getEqR nodeOf t cv fuel r with
    | some y => if (nodeOf y).isSome then getFromR nodeOf valOf t fuel rest y else none
    | none => none

theorem getEq_eq_getEqR (p : Params) (v : View BVal) (t : Time) (cv f : Nat) (x : NodeId) :
    getEq p v t cv f x = getEqR (knodeOf p v) t cv f x := by
  induction f generalizing x with
  | zero => rfl
  | succ f ih =>
    simp only [getEq, getEqR]
    cases knodeOf p v x with
    | none => rfl
    | some n =>
      simp only
      split
      · rfl
      · cases n.searchLte t cv with
        | none => rfl
        | some fd => exact ih fd.y

theorem getFrom_eq_getFromR (p : Params) (v : View BVal) (t : Time) (key : List Nat)
    (x : NodeId) :
    getFrom p v t key x = getFromR (knodeOf p v) (valueOf v) t p.fuel key x := by
  induction key generalizing x with
  | nil => rfl
  | cons c rest ih =>
    cases rest with
    | nil => simp only [getFrom, getFromR, getEq_eq_getEqR]
    | cons d rest =>
      simp only [getFrom, getFromR, getEq_eq_getEqR]
      cases getEqR (knodeOf p v) t c p.fuel x with
      | none => rfl
      | some y =>
        simp only
        split
        · exact ih _
        · rfl

/-! ## Reading through the writer's state -/

/-- Key node x as the writer's state w has it at the transaction's time: none
if the transaction took it back; else its own copy, if it has one; else P@(i-1)'s
(`getNode`). -/
def wNode (c : Ctx) (w : W) (x : NodeId) : Option KNode :=
  if w.taken.contains x then none
  else
    match w.nodes.lookup x with
    | some n => some n
    | none => knodeOf c.p c.view x

/-- The value of node y as the writer's state w has it: a value it made, or
P@(i-1)'s. -/
def wValue (c : Ctx) (w : W) (y : NodeId) : Option Nat :=
  match w.vals.lookup y with
  | some h => some h
  | none => valueOf c.view y

/-- A get at the transaction's time through the writer's state w, from its
super root's space root. -/
def wGet (c : Ctx) (w : W) (key : Key) : Option Nat :=
  getFromR (wNode c w) (wValue c w) c.i c.p.fuel key w.top.rootKey

/-- The writer's context for the transaction after the run ts (`runOps`). -/
def ctxOf (p : Params) (ts : List Tx) : Ctx :=
  { p := p, i := ts.length + 1, view := rootless (view (treeSpec p) (treeRun p ts) ts.length) }

/-- The writer's first state for transaction tx from top node `top`. -/
def wInit (tx : Tx) (top : Top) : W := { next := tx.base, top := top }

/-! ## The three statements -/

/-- The writer's first state reads as P at the time before: through P@(i-1)
without the root, from the space root of the super root it takes. -/
def InitGetOK (p : Params) : Prop :=
  ∀ ts tx, Within p (ts ++ [tx]) → ∀ z top,
    lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z →
    topOf p (ctxOf p ts).view z = .ok top →
    ∀ key, keyWf key = true →
      wGet (ctxOf p ts) (wInit tx top) key = get p (viewOf (treeRun p ts)) ts.length key

/-- Each operation of a transaction within reach changes what the writer's
state reads by itself alone: its key gets its value (a put's, none after a
delete), every other key keeps its value. The writer's refinement of the map,
one operation at a time: every rule of the writer (the splits, the upward
delete, LE-b, the merges, root collapse). Not proved. -/
def OpGetOK (p : Params) : Prop :=
  ∀ ts tx, Within p (ts ++ [tx]) → ∀ z top,
    lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z →
    topOf p (ctxOf p ts).view z = .ok top →
    ∀ pre op post, tx.ops = pre ++ op :: post →
    ∀ r w, (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
    WriterWP (putKv op) (ctxOf p ts) w (fun _ w' => ∀ key, keyWf key = true →
      wGet (ctxOf p ts) w' key =
        if op.key == key then op.value else wGet (ctxOf p ts) w key)

/-- The structure after a transaction reads at its time as the writer's last
state: the lift of the writer's state through `changesOf` and `Struct.apply`. -/
def CommitGetOK (p : Params) : Prop :=
  ∀ ts tx, Within p (ts ++ [tx]) → ∀ noops w,
    runOps p tx.base tx.ops (ts.length + 1) (view (treeSpec p) (treeRun p ts) ts.length) =
      .ok (noops, w) →
    ∀ key, keyWf key = true →
      get p (viewOf (treeRun p (ts ++ [tx]))) (ts.length + 1) key = wGet (ctxOf p ts) w key

/-! ## The composition -/

theorem mapM_snoc_run (done : List Op) (op : Op) (c : Ctx) (w0 w w1 : W) (r : List Bool)
    (a : Bool) (h1 : (done.mapM putKv) c w0 = .ok (r, w)) (h2 : putKv op c w = .ok (a, w1)) :
    ((done ++ [op]).mapM putKv) c w0 = .ok (r ++ [a], w1) := by
  rw [List.mapM_append]
  simp only [List.mapM_cons, List.mapM_nil, bind, ReaderT.bind, StateT.bind, h1, Except.bind,
    h2, pure, ReaderT.pure, StateT.pure, Except.pure, map_pure]

theorem mapM_cons_run (op : Op) (rest : List Op) (c : Ctx) (w w' : W) (r : List Bool)
    (h : ((op :: rest).mapM putKv) c w = .ok (r, w')) :
    ∃ a w1 r', putKv op c w = .ok (a, w1) ∧ (rest.mapM putKv) c w1 = .ok (r', w') := by
  rw [List.mapM_cons] at h
  simp only [bind, ReaderT.bind, StateT.bind, Except.bind] at h
  cases h1 : putKv op c w with
  | error e => rw [h1] at h; cases h
  | ok aw =>
    rcases aw with ⟨a, w1⟩
    rw [h1] at h
    simp only at h
    cases h2 : (rest.mapM putKv) c w1 with
    | error e => rw [h2] at h; cases h
    | ok rw' =>
      rcases rw' with ⟨r', w2⟩
      rw [h2] at h
      simp only [pure, ReaderT.pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      exact ⟨a, w1, r', rfl, by rw [← h.2]; exact h2⟩

/-- The step of the reference over a list of operations. -/
theorem txGet_fold (p : Params) (ho : OpGetOK p) (ts : List Tx) (tx : Tx)
    (hw : Within p (ts ++ [tx])) (z : NodeId) (top : Top)
    (hz : lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z)
    (htop : topOf p (ctxOf p ts).view z = .ok top) :
    ∀ todo done, tx.ops = done ++ todo → ∀ r w,
      (done.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
      ∀ r' w', (todo.mapM putKv) (ctxOf p ts) w = .ok (r', w') →
      ∀ key, keyWf key = true →
        wGet (ctxOf p ts) w' key =
          todo.foldl (fun v op => if op.key == key then op.value else v) (wGet (ctxOf p ts) w key) := by
  intro todo
  induction todo with
  | nil =>
    intro done _ r w _ r' w' hrun key _
    simp only [List.mapM_nil, pure, ReaderT.pure, StateT.pure, Except.pure, Except.ok.injEq,
      Prod.mk.injEq] at hrun
    rw [← hrun.2]
    rfl
  | cons op rest ih =>
    intro done hsplit r w hdone r' w' hrun key hkey
    obtain ⟨a, w1, r1, h1, h2⟩ := mapM_cons_run op rest _ w w' r' hrun
    have hstep := ho ts tx hw z top hz htop done op rest hsplit r w hdone a w1 h1 key hkey
    have hdone' := mapM_snoc_run done op _ _ w w1 r a hdone h1
    rw [ih (done ++ [op]) (by rw [hsplit]; simp) _ w1 hdone' r1 w' h2 key hkey, List.foldl_cons,
      hstep]

theorem runOps_ok (p : Params) (base : NodeId) (ops : List Op) (i : Time) (v : View BVal)
    (noops : List Bool) (w : W) (h : runOps p base ops i v = .ok (noops, w)) :
    ∃ z top, lastTop v = some z ∧ topOf p (rootless v) z = .ok top ∧
      ((ops.mapM putKv) { p := p, i := i, view := rootless v } { next := base, top := top }) =
        .ok (noops, w) := by
  unfold runOps runOpsFrom at h
  cases hz : lastTop v with
  | none => rw [hz] at h; cases h
  | some z =>
    rw [hz] at h
    simp only at h
    cases ht : topOf p (rootless v) z with
    | error e => rw [ht] at h; cases h
    | ok top =>
      rw [ht] at h
      simp only at h
      refine ⟨z, top, rfl, ht, ?_⟩
      exact boundsOK_ok p _ _ _ h

theorem within_last_ok (p : Params) (ts : List Tx) (tx : Tx) (hw : Within p (ts ++ [tx])) :
    ∃ noops w, runOps p tx.base tx.ops (ts.length + 1)
      (view (treeSpec p) (treeRun p ts) ts.length) = .ok (noops, w) := by
  have h := (hw.2 ts.length (by simp)).2
  have hj : (ts ++ [tx])[ts.length]'(by simp) = tx := by simp
  have ht : (ts ++ [tx]).take ts.length = ts := by simp
  rw [hj, ht] at h
  unfold exec? at h
  cases hr : runOps p tx.base tx.ops (ts.length + 1) (view (treeSpec p) (treeRun p ts) ts.length) with
  | error e => rw [hr] at h; simp [Except.map, isOk] at h
  | ok nw => exact ⟨nw.1, nw.2, rfl⟩

/-- TP10's step for one transaction from the three statements about the
writer. -/
theorem txGetOK_of_writer (p : Params) (hi : InitGetOK p) (ho : OpGetOK p)
    (hc : CommitGetOK p) : TxGetOK p := by
  intro ts tx hw key hkey
  obtain ⟨noops, w, hrun⟩ := within_last_ok p ts tx hw
  obtain ⟨z, top, hz, htop, hops⟩ := runOps_ok p _ _ _ _ noops w hrun
  have hs : tx.sorted = true := (hw.1 tx (by simp)).1
  rw [hc ts tx hw noops w hrun key hkey]
  have hfold := txGet_fold p ho ts tx hw z top hz htop tx.ops [] (by simp) [] (wInit tx top)
    (by simp only [List.mapM_nil, pure, ReaderT.pure, StateT.pure, Except.pure])
    noops w hops key hkey
  rw [hfold, hi ts tx hw z top hz htop key hkey, fold_value_find key tx.ops (Tx.keys_nodup tx hs)]
  rfl

/-- TP10 from TP7 and the three statements about the writer. -/
theorem getOK_of_writer (p : Params) (hinv : InvPreserved p) (hi : InitGetOK p)
    (ho : OpGetOK p) (hc : CommitGetOK p) : GetOK p :=
  getOK_of_txGet p hinv (txGetOK_of_writer p hi ho hc)

end SIS.Tree
