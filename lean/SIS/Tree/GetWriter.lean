import SIS.Tree.GetLatest
import SIS.Tree.ScanLatest
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
if the transaction took it back; else its own copy, if it has one; else the
base's (P before the transaction). -/
def wNode (p : Params) (base : View BVal) (w : W) (x : NodeId) : Option KNode :=
  if w.taken.contains x then none
  else
    match w.nodes.lookup x with
    | some n => some n
    | none => knodeOf p base x

/-- The value of node y as the writer's state w has it: none if the
transaction took y back; else a value it made, or the base's. -/
def wValue (base : View BVal) (w : W) (y : NodeId) : Option Nat :=
  if w.taken.contains y then none
  else
    match w.vals.lookup y with
    | some h => some h
    | none => valueOf base y

/-- A get at time i through the writer's state w over the base, from its super
root's space root. -/
def wGet (p : Params) (i : Time) (base : View BVal) (w : W) (key : Key) : Option Nat :=
  getFromR (wNode p base w) (wValue base w) i p.fuel key w.top.rootKey

/-- A get through the writer's state w of the transaction after the run ts: at
the transaction's time, over P before it (`treeRun p ts`, all of it: the writer
itself reads only what is reachable at the time before). -/
def runGet (p : Params) (ts : List Tx) (w : W) (key : Key) : Option Nat :=
  wGet p (ts.length + 1) (viewOf (treeRun p ts)) w key

/-- The writer's context for the transaction after the run ts (`runOps`). -/
def ctxOf (p : Params) (ts : List Tx) : Ctx :=
  { p := p, i := ts.length + 1, view := rootless (view (treeSpec p) (treeRun p ts) ts.length) }

/-- The writer's first state for transaction tx from top node `top`. -/
def wInit (tx : Tx) (top : Top) : W := { next := tx.base, top := top }

/-! ## The three statements -/

/-- The writer's first state reads as P at the time before: from the space
root of the super root it takes. Proved: `initGetOK`. -/
def InitGetOK (p : Params) : Prop :=
  ∀ ts tx, Within p (ts ++ [tx]) → ∀ z top,
    lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z →
    topOf p (ctxOf p ts).view z = .ok top →
    ∀ key, keyWf key = true →
      runGet p ts (wInit tx top) key = get p (viewOf (treeRun p ts)) ts.length key

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
      runGet p ts w' key = if op.key == key then op.value else runGet p ts w key)

/-- The structure after a transaction reads at its time as the writer's last
state: the lift of the writer's state through `changesOf` and `Struct.apply`.
Not proved. -/
def CommitGetOK (p : Params) : Prop :=
  ∀ ts tx, Within p (ts ++ [tx]) → ∀ noops w,
    runOps p tx.base tx.ops (ts.length + 1) (view (treeSpec p) (treeRun p ts) ts.length) =
      .ok (noops, w) →
    ∀ key, keyWf key = true →
      get p (viewOf (treeRun p (ts ++ [tx]))) (ts.length + 1) key = runGet p ts w key

/-! ## The writer's first state -/

theorem view_some (p : Params) (P : Struct BVal) (t : Time) (x : NodeId) (nd : Node BVal)
    (h : view (treeSpec p) P t x = some nd) :
    ∃ nd0, P.get? x = some nd0 ∧ nd = { nd0 with hist := nd0.hist.upTo t } := by
  unfold view at h
  split at h
  · cases h0 : P.get? x with
    | none => rw [h0] at h; cases h
    | some nd0 =>
      rw [h0] at h
      cases h
      exact ⟨nd0, rfl, rfl⟩
  · cases h

theorem upTo_of_timesLE (P : Struct BVal) (t : Time) (hP : StructTimesLE P t) (x : NodeId)
    (nd : Node BVal) (h : P.get? x = some nd) : nd.hist.upTo t = nd.hist :=
  List.filter_eq_self.mpr (fun e he => by
    have := hP _ (get?_mem P x nd h) e he
    simp only [decide_eq_true_eq]
    exact this)

theorem findSome_rootKey (h : History BVal) (t : Time) (y : NodeId)
    (hf : h.findSome? (fun e => match e.val with
      | .rootKey y => some (e.time, y)
      | _ => none) = some (t, y)) :
    h.findSome? (fun e => match e.val with
      | .rootKey y => some y
      | _ => none) = some y := by
  induction h with
  | nil => simp at hf
  | cons e h ih =>
    rw [List.findSome?_cons] at hf ⊢
    cases hv : e.val with
    | rootKey y' =>
      simp only [hv] at hf ⊢
      simp only [Option.some.injEq, Prod.mk.injEq] at hf
      rw [hf.2]
    | key c y' => simp only [hv] at hf ⊢; exact ih hf
    | del cs => simp only [hv] at hf ⊢; exact ih hf
    | skip j z => simp only [hv] at hf ⊢; exact ih hf
    | top z => simp only [hv] at hf ⊢; exact ih hf
    | data d => simp only [hv] at hf ⊢; exact ih hf

/-- The space root that the writer's super root names is P's at the time
before. -/
theorem rootAt_of_writerTop (p : Params) (ts : List Tx) (z : NodeId) (top : Top)
    (hz : lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z)
    (htop : topOf p (ctxOf p ts).view z = .ok top) :
    rootAt (viewOf (treeRun p ts)) ts.length = some top.rootKey := by
  have hP := treeRun_timesLE p ts
  unfold lastTop at hz
  cases hv : view (treeSpec p) (treeRun p ts) ts.length root with
  | none => rw [hv] at hz; cases hz
  | some r =>
    rw [hv] at hz
    obtain ⟨nd0, h0, hr⟩ := view_some p _ _ _ _ hv
    subst hr
    simp only at hz
    have htopAt : topAt (viewOf (treeRun p ts)) ts.length = some z := by
      unfold topAt
      simp only [viewOf, h0]
      exact hz
    unfold rootAt
    rw [htopAt]
    simp only [Option.bind_some]
    unfold topOf at htop
    simp only [ctxOf, rootless] at htop
    by_cases hzr : (z == root) = true
    · simp only [hzr, ↓reduceIte] at htop
      cases htop
    · simp only [hzr, Bool.false_eq_true, ↓reduceIte] at htop
      cases hvz : view (treeSpec p) (treeRun p ts) ts.length z with
      | none => rw [hvz] at htop; cases htop
      | some ndz =>
        rw [hvz] at htop
        obtain ⟨ndz0, hz0, hzr0⟩ := view_some p _ _ _ _ hvz
        subst hzr0
        simp only at htop
        rw [upTo_of_timesLE _ _ hP z ndz0 hz0] at htop
        unfold rootKeyOf
        simp only [viewOf, hz0, Option.bind_some]
        split at htop
        · rename_i t y hf
          simp only [Except.ok.injEq] at htop
          subst htop
          exact findSome_rootKey ndz0.hist t y hf
        · cases htop

/-- `InitGetOK`, proved: the writer's first state reads at the transaction's
time as P at the time before. -/
theorem initGetOK (p : Params) : InitGetOK p := by
  intro ts tx _ z top hz htop key _
  have hroot := rootAt_of_writerTop p ts z top hz htop
  have hn : wNode p (viewOf (treeRun p ts)) (wInit tx top) = knodeOf p (viewOf (treeRun p ts)) := by
    funext x
    simp [wNode, wInit]
  have hval : wValue (viewOf (treeRun p ts)) (wInit tx top) = valueOf (viewOf (treeRun p ts)) := by
    funext y
    simp [wValue, wInit]
  unfold runGet wGet
  rw [hn, hval, ← getFrom_eq_getFromR,
    getFrom_succ_of_timesLE p _ ts.length (treeRun_timesLE p ts)]
  unfold get
  rw [hroot]
  rfl

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
        runGet p ts w' key =
          todo.foldl (fun v op => if op.key == key then op.value else v) (runGet p ts w key) := by
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

/-- TP10's step for one transaction from the two statements about the writer
that are not proved. -/
theorem txGetOK_of_op_commit (p : Params) (ho : OpGetOK p) (hc : CommitGetOK p) :
    TxGetOK p :=
  txGetOK_of_writer p (initGetOK p) ho hc

/-- `LatestGetOK` from the writer's refinement of the map, one operation at a
time, and the lift of its last state. -/
theorem latestGetOK_of_op_commit (p : Params) (ho : OpGetOK p) (hc : CommitGetOK p) :
    LatestGetOK p :=
  latestGetOK_of_txGet p (txGetOK_of_op_commit p ho hc)

/-- TP10 from TP7 and the two statements about the writer. -/
theorem getOK_of_op_commit (p : Params) (hinv : InvPreserved p) (ho : OpGetOK p)
    (hc : CommitGetOK p) : GetOK p :=
  getOK_of_txGet p hinv (txGetOK_of_op_commit p ho hc)

/-- TP11 from TP7 and the two statements about the writer. -/
theorem scanOK_of_op_commit (p : Params) (hinv : InvPreserved p) (ho : OpGetOK p)
    (hc : CommitGetOK p) : ScanOK p :=
  scanOK_of_txGet p hinv (txGetOK_of_op_commit p ho hc)

end SIS.Tree
