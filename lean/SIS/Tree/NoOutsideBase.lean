/-
The runs with no key node outside the level bounds (bergdb 025-03, F1 of
026-16, section 4.2): `NoOutside`, and the run machinery's statements for
such runs. In namespace `SIS.Tree.N`, `Within p ts` is the runs within reach
that are `NoOutside` (`N.Within`), and the run machinery's definitions that
quantify over runs are restated with it (their text as in their own files).
A lemma of the machinery with no hypothesis over runs is used as it is: a
wrapper in N (`n_wrap`) takes `N.Within` where it takes `Within`, and gives
the N form of its conclusion (`ofOld`). The lemmas with hypotheses over runs
are restated in N in NoOutsideRun*.lean, with their proofs as in their own
files; in N the one use of `htb` (`htStart_reachedU`) is proved from
`NoOutside` (every height the writer knows is then at most H).
-/
import SIS.Tree.LatestTop
import SIS.Tree.NoOutsideWrap

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- No transaction of run ts makes a key node outside the level bounds G and
H: the writer's state at the end of each transaction has no node noted in
`outside`. `newKey` notes there every key node it makes outside G and H, and
the note stays, also when the transaction takes the node back; so this says
that every key node any transaction of the run makes, also for a moment in an
operation, is within G and H. For a run of Java's: G and H cover the highest
moment of every transaction, not only the nodes written (024-22, MF1: a delete
can make a root one above the nodes written and take it back). -/
def NoOutside (p : Params) (ts : List Tx) : Prop :=
  ∀ j (h : j < ts.length) noops w,
    execW p ts[j] (j + 1) (view (treeSpec p) (treeRun p (ts.take j)) j) = .ok (noops, w) →
    w.outside = []

theorem noOutside_take (p : Params) (ts : List Tx) (h : NoOutside p ts) (k : Nat) :
    NoOutside p (ts.take k) := by
  intro j hj noops w he
  have hlen : (ts.take k).length = min k ts.length := List.length_take
  have hjts : j < ts.length := by omega
  have hjk : j ≤ k := by omega
  simp only [List.take_take, Nat.min_eq_left hjk, List.getElem_take] at he
  exact h j hjts noops w he

/-- The last transaction of a run with `NoOutside` ends with nothing outside. -/
theorem noOutside_last (p : Params) (ts : List Tx) (tx : Tx) (h : NoOutside p (ts ++ [tx]))
    (noops : List Bool) (w : W)
    (he : execW p tx (ts.length + 1) (view (treeSpec p) (treeRun p ts) ts.length) = .ok (noops, w)) :
    w.outside = [] := by
  have hj : ts.length < (ts ++ [tx]).length := by simp
  have := h ts.length hj noops w
  simp only [List.getElem_append_right (Nat.le_refl _), Nat.sub_self, List.getElem_singleton,
    List.take_append_of_le_length (Nat.le_refl _), List.take_length] at this
  exact this he

/-- At every state that a prefix of the last transaction's operations reaches,
nothing is outside the bounds, so every height the writer knows is at most H. -/
theorem heights_le_H_of_noOutside (p : Params) (ts : List Tx) (tx : Tx)
    (hw : Within p (ts ++ [tx])) (hno : NoOutside p (ts ++ [tx])) (z : NodeId) (top : Top)
    (hz : lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z)
    (htop : topOf p (ctxOf p ts).view z = .ok top) (pre post : List Op)
    (hsplit : tx.ops = pre ++ post) (r : List Bool) (w : W)
    (hpre : (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w)) :
    ∀ x g h, (x, g, h) ∈ w.gh → h ≤ p.H := by
  intro x g h hm
  rcases Nat.lt_or_ge p.H h with hHh | hle
  · exfalso
    have hmk : HeightMarkedPred p w.gh w.outside := by
      letI := heightMarkedFields
      exact fields_ops pre (ctxOf p ts) (wInit tx top)
        (by change HeightMarkedPred p [] []; simp [HeightMarkedPred]) r w hpre
    have hout := hmk x g h hm hHh
    obtain ⟨bs, wE, he⟩ := execW_success_of_within_snoc p ts tx hw
    have hnil := noOutside_last p ts tx hno bs wE he
    unfold execW runOps runOpsFrom at he
    rw [hz] at he
    simp only at he
    have htop' : topOf p (rootless (view (treeSpec p) (treeRun p ts) ts.length)) z = .ok top := htop
    rw [htop'] at he
    simp only at he
    have hrun := boundsOK_ok p _ bs wE he
    have hrun' : ((pre ++ post).mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (bs, wE) := by
      rw [← hsplit]; exact hrun
    obtain ⟨r2, hpost⟩ := mapM_split_run (ctxOf p ts) (wInit tx top) pre post r w bs wE hpre hrun'
    have houtE : (x, g, h) ∈ wE.outside := by
      letI := outsideHasFields (x, g, h)
      exact fields_ops post (ctxOf p ts) w hout r2 wE hpost
    rw [hnil] at houtE
    cases houtE
  · exact hle

namespace N

/-- The runs within reach with no key node outside the level bounds. -/
structure Within (p : Params) (ts : List Tx) : Prop where
  w : SIS.Tree.Within p ts
  no : NoOutside p ts

theorem within_take (p : Params) (ts : List Tx) (hw : Within p ts) (k : Nat) :
    Within p (ts.take k) :=
  ⟨SIS.Tree.within_take p ts hw.w k, noOutside_take p ts hw.no k⟩

/-- `X.ofOld`: X for every run within reach gives X for the runs of `N.Within`. -/
macro "of_old" : tactic => `(tactic| (intro h ts; first
  | (intro tx hw; exact h ts tx hw.w)
  | (intro hw; exact h ts hw.w)))

theorem within_snoc_prefix (p : Params) (ts : List Tx) (tx : Tx)
    (hw : Within p (ts ++ [tx])) : Within p ts := by
  have hh := within_take p (ts ++ [tx]) hw ts.length
  simpa only [List.take_append_of_le_length (Nat.le_refl _), List.take_length] using hh

/-! ## The run machinery's definitions over runs, for the runs of `N.Within` -/

/-- As `SIS.Tree.InvPreserved`, for the runs of `N.Within`. -/
def InvPreserved (p : Params) : Prop :=
  ∀ ts, Within p ts → ∀ t ≤ ts.length, InvOK p (treeRun p ts) t ∧ PointersOK (treeRun p ts)

theorem InvPreserved.ofOld {p : Params} :
    SIS.Tree.InvPreserved p → InvPreserved p := by of_old

/-- As `SIS.Tree.GetOK`, for the runs of `N.Within`. -/
def GetOK (p : Params) : Prop :=
  ∀ ts, Within p ts → ∀ t ≤ ts.length, ∀ key, keyWf key = true →
    get p (viewOf (treeRun p ts)) t key = refGet ts t key

theorem GetOK.ofOld {p : Params} :
    SIS.Tree.GetOK p → GetOK p := by of_old

/-- As `SIS.Tree.ScanOK`, for the runs of `N.Within`. -/
def ScanOK (p : Params) : Prop :=
  ∀ ts, Within p ts →
    ∀ t ≤ ts.length, ∀ (req : ScanReq) (limit : Nat), req.wf = true →
    (scan p (viewOf (treeRun p ts)) t req limit).map (fun kv => (kv.key, kv.h)) =
      refScan ts t req limit

theorem ScanOK.ofOld {p : Params} :
    SIS.Tree.ScanOK p → ScanOK p := by of_old

/-- As `SIS.Tree.LatestGetOK`, for the runs of `N.Within`. -/
def LatestGetOK (p : Params) : Prop :=
  ∀ ts, Within p ts → ∀ key, keyWf key = true →
    get p (viewOf (treeRun p ts)) ts.length key = refGet ts ts.length key

theorem LatestGetOK.ofOld {p : Params} :
    SIS.Tree.LatestGetOK p → LatestGetOK p := by of_old

/-- As `SIS.Tree.TxGetOK`, for the runs of `N.Within`. -/
def TxGetOK (p : Params) : Prop :=
  ∀ ts tx, Within p (ts ++ [tx]) → ∀ key, keyWf key = true →
    get p (viewOf (treeRun p (ts ++ [tx]))) (ts.length + 1) key =
      txValue tx key (get p (viewOf (treeRun p ts)) ts.length key)

theorem TxGetOK.ofOld {p : Params} :
    SIS.Tree.TxGetOK p → TxGetOK p := by of_old

/-- As `SIS.Tree.LatestInvOK`, for the runs of `N.Within`. -/
def LatestInvOK (p : Params) : Prop :=
  ∀ ts, Within p ts → InvOK p (treeRun p ts) ts.length

theorem LatestInvOK.ofOld {p : Params} :
    SIS.Tree.LatestInvOK p → LatestInvOK p := by of_old

/-- As `SIS.Tree.LatestScanOK`, for the runs of `N.Within`. -/
def LatestScanOK (p : Params) : Prop :=
  ∀ ts, Within p ts → ∀ (req : ScanReq) (limit : Nat), req.wf = true →
    (scan p (viewOf (treeRun p ts)) ts.length req limit).map (fun kv => (kv.key, kv.h)) =
      refScan ts ts.length req limit

theorem LatestScanOK.ofOld {p : Params} :
    SIS.Tree.LatestScanOK p → LatestScanOK p := by of_old

/-- As `SIS.Tree.InitGetOK`, for the runs of `N.Within`. -/
def InitGetOK (p : Params) : Prop :=
  ∀ ts tx, Within p (ts ++ [tx]) → ∀ z top,
    lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z →
    topOf p (ctxOf p ts).view z = .ok top →
    ∀ key, keyWf key = true →
      runGet p ts (wInit tx top) key = get p (viewOf (treeRun p ts)) ts.length key

theorem InitGetOK.ofOld {p : Params} :
    SIS.Tree.InitGetOK p → InitGetOK p := by of_old

/-- As `SIS.Tree.OpGetOK`, for the runs of `N.Within`. -/
def OpGetOK (p : Params) : Prop :=
  ∀ ts tx, Within p (ts ++ [tx]) → ∀ z top,
    lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z →
    topOf p (ctxOf p ts).view z = .ok top →
    ∀ pre op post, tx.ops = pre ++ op :: post →
    ∀ r w, (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
    WriterWP (putKv op) (ctxOf p ts) w (fun _ w' => ∀ key, keyWf key = true →
      runGet p ts w' key = if op.key == key then op.value else runGet p ts w key)

theorem OpGetOK.ofOld {p : Params} :
    SIS.Tree.OpGetOK p → OpGetOK p := by of_old

/-- As `SIS.Tree.CommitGetOK`, for the runs of `N.Within`. -/
def CommitGetOK (p : Params) : Prop :=
  ∀ ts tx, Within p (ts ++ [tx]) → ∀ noops w,
    runOps p tx.base tx.ops (ts.length + 1) (view (treeSpec p) (treeRun p ts) ts.length) =
      .ok (noops, w) →
    ∀ key, keyWf key = true →
      get p (viewOf (treeRun p (ts ++ [tx]))) (ts.length + 1) key = runGet p ts w key

theorem CommitGetOK.ofOld {p : Params} :
    SIS.Tree.CommitGetOK p → CommitGetOK p := by of_old

/-- As `SIS.Tree.CommitLiftOK`, for the runs of `N.Within`. -/
def CommitLiftOK (p : Params) : Prop :=
  ∀ ts tx, Within p (ts ++ [tx]) → ∀ noops w,
    runOps p tx.base tx.ops (ts.length + 1) (view (treeSpec p) (treeRun p ts) ts.length) =
      .ok (noops, w) →
    (∀ x, knodeOf p (viewOf (treeRun p (ts ++ [tx]))) x = wNode p (viewOf (treeRun p ts)) w x) ∧
    (∀ x ∈ w.taken, tx.base ≤ x) ∧
    (w.newTop = true → w.taken.contains w.top.id = false)

theorem CommitLiftOK.ofOld {p : Params} :
    SIS.Tree.CommitLiftOK p → CommitLiftOK p := by of_old

/-- As `SIS.Tree.OverlayLiftOK`, for the runs of `N.Within`. -/
def OverlayLiftOK (p : Params) : Prop :=
  ∀ ts tx, Within p (ts ++ [tx]) → ∀ noops w,
    runOps p tx.base tx.ops (ts.length + 1) (view (treeSpec p) (treeRun p ts) ts.length) =
      .ok (noops, w) →
    (∀ x n, w.nodes.lookup x = some n → w.taken.contains x = false →
      knodeOf p (viewOf (treeRun p (ts ++ [tx]))) x = some n) ∧
    (∀ x ∈ w.taken, tx.base ≤ x) ∧
    (w.newTop = true → w.taken.contains w.top.id = false)

theorem OverlayLiftOK.ofOld {p : Params} :
    SIS.Tree.OverlayLiftOK p → OverlayLiftOK p := by of_old

/-- As `SIS.Tree.OpGetOKUnder`, for the runs of `N.Within`. -/
def OpGetOKUnder (p : Params) (R : Struct BVal → Time → Prop) : Prop :=
  ∀ ts tx, Within p (ts ++ [tx]) → R (treeRun p ts) ts.length → ∀ z top,
    lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z →
    topOf p (ctxOf p ts).view z = .ok top →
    ∀ pre op post, tx.ops = pre ++ op :: post →
    ∀ r w, (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
    WriterWP (putKv op) (ctxOf p ts) w (fun _ w' => ∀ key, keyWf key = true →
      runGet p ts w' key = if op.key == key then op.value else runGet p ts w key)

theorem OpGetOKUnder.ofOld {p : Params} {R : Struct BVal → Time → Prop} :
    SIS.Tree.OpGetOKUnder p R → OpGetOKUnder p R := by of_old

/-- As `SIS.Tree.OverlayLiftOKUnder`, for the runs of `N.Within`. -/
def OverlayLiftOKUnder (p : Params) (R : Struct BVal → Time → Prop) : Prop :=
  ∀ ts tx, Within p (ts ++ [tx]) → R (treeRun p ts) ts.length → ∀ noops w,
    runOps p tx.base tx.ops (ts.length + 1) (view (treeSpec p) (treeRun p ts) ts.length) =
      .ok (noops, w) →
    (∀ x n, w.nodes.lookup x = some n → w.taken.contains x = false →
      knodeOf p (viewOf (treeRun p (ts ++ [tx]))) x = some n) ∧
    (∀ x ∈ w.taken, tx.base ≤ x) ∧
    (w.newTop = true → w.taken.contains w.top.id = false)

theorem OverlayLiftOKUnder.ofOld {p : Params} {R : Struct BVal → Time → Prop} :
    SIS.Tree.OverlayLiftOKUnder p R → OverlayLiftOKUnder p R := by of_old

/-- As `SIS.Tree.OpTreeOK`, for the runs of `N.Within`. -/
def OpTreeOK (p : Params) : Prop :=
  ∀ ts tx, Within p (ts ++ [tx]) → ∀ z top,
    lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z →
    topOf p (ctxOf p ts).view z = .ok top →
    ∀ pre op post, tx.ops = pre ++ op :: post →
    ∀ r w, (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
    WriterTreeOK p (treeRun p ts) (ts.length + 1) w →
    WriterWP (putKv op) (ctxOf p ts) w (fun _ w' =>
      WriterTreeOK p (treeRun p ts) (ts.length + 1) w')

theorem OpTreeOK.ofOld {p : Params} :
    SIS.Tree.OpTreeOK p → OpTreeOK p := by of_old

/-- As `SIS.Tree.OpPutInvOK`, for the runs of `N.Within`. -/
def OpPutInvOK (p : Params) (R : Struct BVal → Time → Prop) : Prop :=
  ∀ ts tx, Within p (ts ++ [tx]) → R (treeRun p ts) ts.length → ∀ z top,
    lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z →
    topOf p (ctxOf p ts).view z = .ok top →
    ∀ pre op post, tx.ops = pre ++ op :: post →
    ∀ r w, (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
    PutInv (ctxOf p ts) (viewOf (treeRun p ts)) w →
    WriterWP (putKv op) (ctxOf p ts) w (fun _ w' =>
      WriterTreeOK p (treeRun p ts) (ts.length + 1) w' →
      PutInv (ctxOf p ts) (viewOf (treeRun p ts)) w')

theorem OpPutInvOK.ofOld {p : Params} {R : Struct BVal → Time → Prop} :
    SIS.Tree.OpPutInvOK p R → OpPutInvOK p R := by of_old

/-- As `SIS.Tree.TakeBackOKUnder`, for the runs of `N.Within`. -/
def TakeBackOKUnder (p : Params) (R : Struct BVal → Time → Prop) : Prop :=
  ∀ ts tx, Within p (ts ++ [tx]) → R (treeRun p ts) ts.length → ∀ noops w,
    runOps p tx.base tx.ops (ts.length + 1) (view (treeSpec p) (treeRun p ts) ts.length) =
      .ok (noops, w) → TakeBackEnd w

theorem TakeBackOKUnder.ofOld {p : Params} {R : Struct BVal → Time → Prop} :
    SIS.Tree.TakeBackOKUnder p R → TakeBackOKUnder p R := by of_old

/-- As `SIS.Tree.OpGetPutInvOK`, for the runs of `N.Within`. -/
def OpGetPutInvOK (p : Params) (R : Struct BVal → Time → Prop) : Prop :=
  ∀ ts tx, Within p (ts ++ [tx]) → R (treeRun p ts) ts.length → ∀ z top,
    lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z →
    topOf p (ctxOf p ts).view z = .ok top →
    ∀ pre op post, tx.ops = pre ++ op :: post →
    ∀ r w, (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
    PutInv (ctxOf p ts) (viewOf (treeRun p ts)) w →
    WriterWP (putKv op) (ctxOf p ts) w (fun _ w' => ∀ key, keyWf key = true →
      runGet p ts w' key = if op.key == key then op.value else runGet p ts w key)

theorem OpGetPutInvOK.ofOld {p : Params} {R : Struct BVal → Time → Prop} :
    SIS.Tree.OpGetPutInvOK p R → OpGetPutInvOK p R := by of_old

/-- As `SIS.Tree.OpRangeOK`, for the runs of `N.Within`. -/
def OpRangeOK (p : Params) (R : Struct BVal → Time → Prop) : Prop :=
  ∀ ts tx, Within p (ts ++ [tx]) → R (treeRun p ts) ts.length → ∀ z top,
    lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z →
    topOf p (ctxOf p ts).view z = .ok top →
    ∀ pre op post, tx.ops = pre ++ op :: post →
    ∀ r w, (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
    PutInv (ctxOf p ts) (viewOf (treeRun p ts)) w →
    RangeOrder (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey →
    WriterWP (putKv op) (ctxOf p ts) w (fun _ w' =>
      WriterTreeOK p (treeRun p ts) (ts.length + 1) w' →
      RangeOrder (wNode p (viewOf (treeRun p ts)) w') (ts.length + 1) w'.top.rootKey)

theorem OpRangeOK.ofOld {p : Params} {R : Struct BVal → Time → Prop} :
    SIS.Tree.OpRangeOK p R → OpRangeOK p R := by of_old

/-- As `SIS.Tree.TxSegFitsOK`, for the runs of `N.Within`. -/
def TxSegFitsOK (p : Params) (R : Struct BVal → Time → Prop) : Prop :=
  ∀ ts tx, Within p (ts ++ [tx]) → R (treeRun p ts) ts.length → ∀ z top,
    lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z →
    topOf p (ctxOf p ts).view z = .ok top →
    ∀ pre post, tx.ops = pre ++ post → ∀ r w,
    (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
    SegFits (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) (p.fuel - 1) w.top.rootKey

theorem TxSegFitsOK.ofOld {p : Params} {R : Struct BVal → Time → Prop} :
    SIS.Tree.TxSegFitsOK p R → TxSegFitsOK p R := by of_old

/-- As `SIS.Tree.OpGetCaseOK`, for the runs of `N.Within`. -/
def OpGetCaseOK (p : Params) (R : Struct BVal → Time → Prop)
    (P : Ctx → View BVal → W → Op → Prop) : Prop :=
  ∀ ts tx, Within p (ts ++ [tx]) → R (treeRun p ts) ts.length → ∀ z top,
    lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z →
    topOf p (ctxOf p ts).view z = .ok top →
    ∀ pre op post, tx.ops = pre ++ op :: post →
    ∀ r w, (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
    PutInv (ctxOf p ts) (viewOf (treeRun p ts)) w →
    RangeOrder (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey →
    P (ctxOf p ts) (viewOf (treeRun p ts)) w op →
    WriterWP (putKv op) (ctxOf p ts) w (fun _ w' =>
      SegFits (wNode p (viewOf (treeRun p ts)) w') (ts.length + 1) (p.fuel - 1) w'.top.rootKey →
      ∀ key, keyWf key = true →
        runGet p ts w' key = if op.key == key then op.value else runGet p ts w key)

theorem OpGetCaseOK.ofOld {p : Params} {R : Struct BVal → Time → Prop} {P : Ctx → View BVal → W → Op → Prop} :
    SIS.Tree.OpGetCaseOK p R P → OpGetCaseOK p R P := by of_old

/-- As `SIS.Tree.OpCaseOK`, for the runs of `N.Within`. -/
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

theorem OpCaseOK.ofOld {p : Params} {R : Struct BVal → Time → Prop} {Q : List Tx → Op → W → W → Prop} {P : Ctx → View BVal → W → Op → Prop} :
    SIS.Tree.OpCaseOK p R Q P → OpCaseOK p R Q P := by of_old

/-- As `SIS.Tree.TakenNotValOK`, for the runs of `N.Within`. -/
def TakenNotValOK (p : Params) (R : Struct BVal → Time → Prop) : Prop :=
  ∀ ts tx, Within p (ts ++ [tx]) → R (treeRun p ts) ts.length → ∀ noops w,
    runOps p tx.base tx.ops (ts.length + 1) (view (treeSpec p) (treeRun p ts) ts.length) =
      .ok (noops, w) → ∀ x ∈ w.taken, x ∉ w.vals.map (·.1)

theorem TakenNotValOK.ofOld {p : Params} {R : Struct BVal → Time → Prop} :
    SIS.Tree.TakenNotValOK p R → TakenNotValOK p R := by of_old

/-- As `SIS.Tree.OpTreeOKUnder`, for the runs of `N.Within`. -/
def OpTreeOKUnder (p : Params) (R : Struct BVal → Time → Prop) : Prop :=
  ∀ ts tx, Within p (ts ++ [tx]) → R (treeRun p ts) ts.length → ∀ z top,
    lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z →
    topOf p (ctxOf p ts).view z = .ok top →
    ∀ pre op post, tx.ops = pre ++ op :: post →
    ∀ r w, (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
    WriterTreeOK p (treeRun p ts) (ts.length + 1) w →
    WriterWP (putKv op) (ctxOf p ts) w (fun _ w' =>
      WriterTreeOK p (treeRun p ts) (ts.length + 1) w')

theorem OpTreeOKUnder.ofOld {p : Params} {R : Struct BVal → Time → Prop} :
    SIS.Tree.OpTreeOKUnder p R → OpTreeOKUnder p R := by of_old

/-- As `SIS.Tree.StateOK`, for the runs of `N.Within`. -/
def StateOK (p : Params) (R : Struct BVal → Time → Prop) (S : List Tx → Tx → W → Prop) : Prop :=
  ∀ ts tx, Within p (ts ++ [tx]) → R (treeRun p ts) ts.length → ∀ z top,
    lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z →
    topOf p (ctxOf p ts).view z = .ok top →
    ∀ pre post, tx.ops = pre ++ post → ∀ r w,
    (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) → S ts tx w

theorem StateOK.ofOld {p : Params} {R : Struct BVal → Time → Prop} {S : List Tx → Tx → W → Prop} :
    SIS.Tree.StateOK p R S → StateOK p R S := by of_old

/-- As `SIS.Tree.BaseStartOK`, for the runs of `N.Within`. -/
def BaseStartOK (p : Params) (R : Struct BVal → Time → Prop) : Prop :=
  ∀ ts tx, Within p (ts ++ [tx]) → R (treeRun p ts) ts.length → ∀ q qn,
    knodeOf p (viewOf (treeRun p ts)) q = some qn → ∃ s, s < ts.length + 1 ∧ qn.firstTime = some s

theorem BaseStartOK.ofOld {p : Params} {R : Struct BVal → Time → Prop} :
    SIS.Tree.BaseStartOK p R → BaseStartOK p R := by of_old

/-- As `SIS.Tree.OpGetCaseOK'`, for the runs of `N.Within`. -/
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

theorem OpGetCaseOK'.ofOld {p : Params} {R : Struct BVal → Time → Prop} {P : Ctx → View BVal → W → Op → Prop} :
    SIS.Tree.OpGetCaseOK' p R P → OpGetCaseOK' p R P := by of_old

/-- As `SIS.Tree.OpJ2OK`, for the runs of `N.Within`. -/
def OpJ2OK (p : Params) (R : Struct BVal → Time → Prop) (S : List Tx → Tx → W → Prop) : Prop :=
  ∀ ts tx, Within p (ts ++ [tx]) → R (treeRun p ts) ts.length → ∀ z top,
    lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z →
    topOf p (ctxOf p ts).view z = .ok top →
    ∀ pre op post, tx.ops = pre ++ op :: post →
    ∀ r w, (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
    WriterTreeOK p (treeRun p ts) (ts.length + 1) w → S ts tx w →
    J2At p (treeRun p ts) (ts.length + 1) tx.base w →
    WriterWP (putKv op) (ctxOf p ts) w (fun _ w' =>
      WriterTreeOK p (treeRun p ts) (ts.length + 1) w' →
      J2At p (treeRun p ts) (ts.length + 1) tx.base w')

theorem OpJ2OK.ofOld {p : Params} {R : Struct BVal → Time → Prop} {S : List Tx → Tx → W → Prop} :
    SIS.Tree.OpJ2OK p R S → OpJ2OK p R S := by of_old

/-- As `SIS.Tree.OpJ2CaseOK`, for the runs of `N.Within`. -/
def OpJ2CaseOK (p : Params) (R : Struct BVal → Time → Prop) (S : List Tx → Tx → W → Prop)
    (P : Ctx → View BVal → W → Op → Prop) : Prop :=
  ∀ ts tx, Within p (ts ++ [tx]) → R (treeRun p ts) ts.length → ∀ z top,
    lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z →
    topOf p (ctxOf p ts).view z = .ok top →
    ∀ pre op post, tx.ops = pre ++ op :: post →
    ∀ r w, (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
    WriterTreeOK p (treeRun p ts) (ts.length + 1) w → S ts tx w →
    J2At p (treeRun p ts) (ts.length + 1) tx.base w →
    P (ctxOf p ts) (viewOf (treeRun p ts)) w op →
    WriterWP (putKv op) (ctxOf p ts) w (fun _ w' =>
      WriterTreeOK p (treeRun p ts) (ts.length + 1) w' →
      J2At p (treeRun p ts) (ts.length + 1) tx.base w')

theorem OpJ2CaseOK.ofOld {p : Params} {R : Struct BVal → Time → Prop} {S : List Tx → Tx → W → Prop} {P : Ctx → View BVal → W → Op → Prop} :
    SIS.Tree.OpJ2CaseOK p R S P → OpJ2CaseOK p R S P := by of_old

/-- As `SIS.Tree.DelStepsOK`, for the runs of `N.Within`. -/
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

theorem DelStepsOK.ofOld {p : Params} {R : Struct BVal → Time → Prop} :
    SIS.Tree.DelStepsOK p R → DelStepsOK p R := by of_old

/-- As `SIS.Tree.DelStepsCaseOK`, for the runs of `N.Within`. -/
def DelStepsCaseOK (p : Params) (R : Struct BVal → Time → Prop)
    (P : Ctx → View BVal → W → Op → Prop) : Prop :=
  ∀ ts tx, Within p (ts ++ [tx]) → R (treeRun p ts) ts.length → ∀ z top,
    lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z →
    topOf p (ctxOf p ts).view z = .ok top →
    ∀ pre op post, tx.ops = pre ++ op :: post →
    ∀ r w, (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
    PutInv (ctxOf p ts) (viewOf (treeRun p ts)) w →
    RangeOrder (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey →
    SegFits (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) (p.fuel - 1) w.top.rootKey →
    ∀ key, op = .del key → P (ctxOf p ts) (viewOf (treeRun p ts)) w op →
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

theorem DelStepsCaseOK.ofOld {p : Params} {R : Struct BVal → Time → Prop} {P : Ctx → View BVal → W → Op → Prop} :
    SIS.Tree.DelStepsCaseOK p R P → DelStepsCaseOK p R P := by of_old

/-- As `SIS.Tree.DelStepsJ2OK`, for the runs of `N.Within`. -/
def DelStepsJ2OK (p : Params) (R : Struct BVal → Time → Prop) (S : List Tx → Tx → W → Prop) : Prop :=
  ∀ ts tx, Within p (ts ++ [tx]) → R (treeRun p ts) ts.length → ∀ z top,
    lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z →
    topOf p (ctxOf p ts).view z = .ok top →
    ∀ pre op post, tx.ops = pre ++ op :: post →
    ∀ r w, (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
    S ts tx w → TakeJ2 (ctxOf p ts) (viewOf (treeRun p ts)) tx.base w →
    ∀ key, op = .del key → p.merges = true →
    (∀ g h v, DelInvJ (ctxOf p ts) (viewOf (treeRun p ts)) w key (p.fuel + 1) (kindOracleOf p (treeRun p ts)) tx.base tx.base v →
      WriterWP (afterDelete key g h) (ctxOf p ts) v (fun _ v' => DelInvJ (ctxOf p ts) (viewOf (treeRun p ts)) w key (p.fuel + 1) (kindOracleOf p (treeRun p ts)) tx.base tx.base v')) →
    (∀ g h merged v, DelInvJ (ctxOf p ts) (viewOf (treeRun p ts)) w key (p.fuel + 1) (kindOracleOf p (treeRun p ts)) tx.base tx.base v →
      WriterWP (mergeUp key g p.fuel h merged) (ctxOf p ts) v (fun _ v' => DelInvJ (ctxOf p ts) (viewOf (treeRun p ts)) w key (p.fuel + 1) (kindOracleOf p (treeRun p ts)) tx.base tx.base v')) →
    (∀ seg v, DelInvJ (ctxOf p ts) (viewOf (treeRun p ts)) w key (p.fuel + 1) (kindOracleOf p (treeRun p ts)) tx.base tx.base v →
      WriterWP (collapseRoot key seg p.fuel) (ctxOf p ts) v (fun _ v' => DelInvJ (ctxOf p ts) (viewOf (treeRun p ts)) w key (p.fuel + 1) (kindOracleOf p (treeRun p ts)) tx.base tx.base v')) →
    WriterWP (putKv op) (ctxOf p ts) w (fun _ w' => TakeJ2 (ctxOf p ts) (viewOf (treeRun p ts)) tx.base w')

theorem DelStepsJ2OK.ofOld {p : Params} {R : Struct BVal → Time → Prop} {S : List Tx → Tx → W → Prop} :
    SIS.Tree.DelStepsJ2OK p R S → DelStepsJ2OK p R S := by of_old

/-- As `SIS.Tree.DelStepsCaseJ2OK`, for the runs of `N.Within`. -/
def DelStepsCaseJ2OK (p : Params) (R : Struct BVal → Time → Prop) (S : List Tx → Tx → W → Prop)
    (P : Ctx → View BVal → W → Op → Prop) : Prop :=
  ∀ ts tx, Within p (ts ++ [tx]) → R (treeRun p ts) ts.length → ∀ z top,
    lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z →
    topOf p (ctxOf p ts).view z = .ok top →
    ∀ pre op post, tx.ops = pre ++ op :: post →
    ∀ r w, (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
    S ts tx w → TakeJ2 (ctxOf p ts) (viewOf (treeRun p ts)) tx.base w →
    ∀ key, op = .del key → P (ctxOf p ts) (viewOf (treeRun p ts)) w op →
    (∀ g h v, DelInvJ (ctxOf p ts) (viewOf (treeRun p ts)) w key (p.fuel + 1) (kindOracleOf p (treeRun p ts)) tx.base tx.base v →
      WriterWP (afterDelete key g h) (ctxOf p ts) v (fun _ v' => DelInvJ (ctxOf p ts) (viewOf (treeRun p ts)) w key (p.fuel + 1) (kindOracleOf p (treeRun p ts)) tx.base tx.base v')) →
    (∀ g h merged v, DelInvJ (ctxOf p ts) (viewOf (treeRun p ts)) w key (p.fuel + 1) (kindOracleOf p (treeRun p ts)) tx.base tx.base v →
      WriterWP (mergeUp key g p.fuel h merged) (ctxOf p ts) v (fun _ v' => DelInvJ (ctxOf p ts) (viewOf (treeRun p ts)) w key (p.fuel + 1) (kindOracleOf p (treeRun p ts)) tx.base tx.base v')) →
    (∀ seg v, DelInvJ (ctxOf p ts) (viewOf (treeRun p ts)) w key (p.fuel + 1) (kindOracleOf p (treeRun p ts)) tx.base tx.base v →
      WriterWP (collapseRoot key seg p.fuel) (ctxOf p ts) v (fun _ v' => DelInvJ (ctxOf p ts) (viewOf (treeRun p ts)) w key (p.fuel + 1) (kindOracleOf p (treeRun p ts)) tx.base tx.base v')) →
    WriterWP (putKv op) (ctxOf p ts) w (fun _ w' => TakeJ2 (ctxOf p ts) (viewOf (treeRun p ts)) tx.base w')

theorem DelStepsCaseJ2OK.ofOld {p : Params} {R : Struct BVal → Time → Prop} {S : List Tx → Tx → W → Prop} {P : Ctx → View BVal → W → Op → Prop} :
    SIS.Tree.DelStepsCaseJ2OK p R S P → DelStepsCaseJ2OK p R S P := by of_old

/-- As `SIS.Tree.OpHtDelOKUnder`, for the runs of `N.Within`. -/
def OpHtDelOKUnder (p : Params) (R : Struct BVal → Time → Prop) : Prop :=
  ∀ ts tx, Within p (ts ++ [tx]) → R (treeRun p ts) ts.length → ∀ z top,
    lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z →
    topOf p (ctxOf p ts).view z = .ok top →
    ∀ pre key post, tx.ops = pre ++ Op.del key :: post →
    ∀ r w, (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
    ViewHtOK (htOracleOf p (treeRun p ts)) tx.base (ctxOf p ts) →
    ViewKlongsWf p (ctxOf p ts).view → Book tx.base (ctxOf p ts) w → WriterKlongsWf w →
    HtInv (htOracleOf p (treeRun p ts)) tx.base (ctxOf p ts) w →
    WriterWP (putKv (.del key)) (ctxOf p ts) w
      (fun _ v => HtInv (htOracleOf p (treeRun p ts)) tx.base (ctxOf p ts) v)

theorem OpHtDelOKUnder.ofOld {p : Params} {R : Struct BVal → Time → Prop} :
    SIS.Tree.OpHtDelOKUnder p R → OpHtDelOKUnder p R := by of_old

/-- As `SIS.Tree.DelStepsCaseQd`, for the runs of `N.Within`. -/
def DelStepsCaseQd (p : Params) (R : Struct BVal → Time → Prop)
    (P : Ctx → View BVal → W → Op → Prop) : Prop :=
  ∀ ts tx, Within p (ts ++ [tx]) → R (treeRun p ts) ts.length → ∀ z top,
    lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z →
    topOf p (ctxOf p ts).view z = .ok top →
    ∀ pre op post, tx.ops = pre ++ op :: post →
    ∀ r w, (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
    PutInv (ctxOf p ts) (viewOf (treeRun p ts)) w →
    RangeOrder (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey →
    SegFits (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) (p.fuel - 1) w.top.rootKey →
    ∀ key, op = .del key → P (ctxOf p ts) (viewOf (treeRun p ts)) w op →
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
    WriterWP (putKv op) (ctxOf p ts) w (fun _ w' => QdW p ts w')

theorem DelStepsCaseQd.ofOld {p : Params} {R : Struct BVal → Time → Prop} {P : Ctx → View BVal → W → Op → Prop} :
    SIS.Tree.DelStepsCaseQd p R P → DelStepsCaseQd p R P := by of_old

/-- As `SIS.Tree.DelStepsQdL`, for the runs of `N.Within`. -/
def DelStepsQdL (p : Params) (R : Struct BVal → Time → Prop) : Prop :=
  DelStepsCaseQd p R (fun c base w op => (∃ key, op = .del key ∧ c.p.merges = true) ∧
    LiveCounts c.p (wNode c.p base w) c.i w.top.rootKey)

theorem DelStepsQdL.ofOld {p : Params} {R : Struct BVal → Time → Prop} :
    SIS.Tree.DelStepsQdL p R → DelStepsQdL p R := by of_old

end N

-- the lemmas of the run machinery used by NoOutsideRun*.lean and LatestTopNoOutside.lean, in N
n_wrap SIS.Tree.treeRun_get_snoc_past SIS.Tree.treeRun_get_eq_prefix SIS.Tree.getOK_of_latest SIS.Tree.latestGetOK_of_txGet SIS.Tree.getOK_of_txGet SIS.Tree.scanOK_of_latest_invariant SIS.Tree.scanOK_of_latest SIS.Tree.rootContents_eq_refKvs SIS.Tree.latestScanOK_of_latestGet SIS.Tree.scanOK_of_latestGet SIS.Tree.scanOK_of_txGet SIS.Tree.txGet_fold SIS.Tree.txGetOK_of_writer SIS.Tree.txGetOK_of_op_commit SIS.Tree.getOK_of_op_commit SIS.Tree.scanOK_of_op_commit SIS.Tree.commitGetOK_of_lift SIS.Tree.getOK_of_op_lift SIS.Tree.scanOK_of_op_lift SIS.Tree.commitLiftOK_of_overlay SIS.Tree.getOK_of_op_overlay SIS.Tree.scanOK_of_op_overlay SIS.Tree.invPreserved_of_latest SIS.Tree.overlayLiftOKUnder_mono SIS.Tree.opGetOK_of_under SIS.Tree.overlayLiftOK_of_under SIS.Tree.getOK_of_under SIS.Tree.scanOK_of_under SIS.Tree.writerTreeOK_fold SIS.Tree.writerTreeOK_reached SIS.Tree.invPreserved_of_parts SIS.Tree.runLinksOK_of_pointers SIS.Tree.treeRun_sizeOK_of_pointers SIS.Tree.invPreserved_of_latest_pointers SIS.Tree.putInv_reached SIS.Tree.opGetOKUnder_of_putInv SIS.Tree.getOK_of_putInv SIS.Tree.scanOK_of_putInv SIS.Tree.rangeOrder_reached SIS.Tree.treeRun_kindsAllOK SIS.Tree.opGetPutInvOK_of_cases SIS.Tree.getOK_scanOK_of_open SIS.Tree.getOK_scanOK_of_open_runOK SIS.Tree.getOK_scanOK_of_open_cases SIS.Tree.getOK_scanOK_of_open_merges SIS.Tree.opCaseOK_of_cases SIS.Tree.opCaseOK_of_cases_merges SIS.Tree.joint_reached SIS.Tree.opRangeOK_of_any SIS.Tree.opPutInvOK_of_any SIS.Tree.opTreeOK_of_any SIS.Tree.getOK_scanOK_of_cases_merges SIS.Tree.live_reached SIS.Tree.opCaseOK_putNewSeg_of_parts SIS.Tree.getOK_scanOK_of_cases_merges_open SIS.Tree.latestGetOK_of_getOK SIS.Tree.latestScanOK_of_scanOK SIS.Tree.writerTreeOK_foldU SIS.Tree.writerTreeOK_reachedU SIS.Tree.treeAt_stepU SIS.Tree.invOK_snocR SIS.Tree.opCaseOK_anti SIS.Tree.opTreeOKUnder_of_cases SIS.Tree.putInvStateOK_of_cases SIS.Tree.rangeStateOK_of_cases SIS.Tree.opGetCaseOK_of' SIS.Tree.j2_reached SIS.Tree.takeBackOKUnder_of_opsJ2 SIS.Tree.runTree_jointJ2 SIS.Tree.innerChildren_reached SIS.Tree.opJ2OK_of_cases SIS.Tree.opJ2Case_putNewSeg SIS.Tree.delStepsOK_of_cases SIS.Tree.kd_context SIS.Tree.delStepsCaseOK_room SIS.Tree.delStepsCaseOK_emptyRoom SIS.Tree.delStepsCaseOK_or SIS.Tree.delStepsCaseOK_emptyRoot SIS.Tree.opGetCaseOK'_delMerge SIS.Tree.opGetCaseOK_delMerge SIS.Tree.delStepsJ2OK_of_cases SIS.Tree.delStepsCaseJ2OK_or SIS.Tree.opJ2Case_delMergeR SIS.Tree.runTreeQ_of_cases3S SIS.Tree.runTreeQ_of_cases4S SIS.Tree.runTreeQ_of_cases_merges4S SIS.Tree.runTreeQ_of_mergesS SIS.Tree.dead_reached SIS.Tree.deadAllOK_snocR SIS.Tree.ht_reachedU SIS.Tree.execW_htCacheU SIS.Tree.htStart_reachedU SIS.Tree.txSegFitsOK_of_takeBelowDelRHU SIS.Tree.txSegFitsOK_of_takeBelowDelR2U SIS.Tree.delStepsCaseOK_fullH SIS.Tree.delStepsCaseJ2OK_fullRH SIS.Tree.opCaseOK_L_of_any SIS.Tree.jointLive_reached SIS.Tree.opCaseOK_any_of_L SIS.Tree.liveStateOK_of_L SIS.Tree.opCaseOK_of_cases_mergesL SIS.Tree.opCaseOK_of_any SIS.Tree.delStepsCaseQd_fullH SIS.Tree.opCaseOK_qdW_delMergeRL SIS.Tree.opCaseOK_treeInvRange_delMergeRL SIS.Tree.opCaseOK_or SIS.Tree.liveCase_delMerge_of_rest SIS.Tree.deadCase_delMergeL_of_rest SIS.Tree.delStepsCaseOK_emptyCascLHG SIS.Tree.delStepsCaseJ2OK_emptyCascRLHG SIS.Tree.delStepsCaseQd_emptyCascLHG SIS.Tree.delStepsOK_of_open SIS.Tree.delStepsJ2OK_of_openR SIS.Tree.delStepsQdL_of_openR SIS.Tree.opCaseOK_of_open SIS.Tree.delStepsOK_of_within SIS.Tree.heightAllOK_snocU SIS.Tree.opCaseOK_of_within SIS.Tree.latestQD_snocR
-- the put cases that the top theorem of 2026-11-14 used (025-02), which N's form of it uses
n_wrap_these SIS.Tree.liveCase_putLeafRoom SIS.Tree.liveCase_putLeafFull SIS.Tree.liveCase_putNewSeg1Room
  SIS.Tree.liveCase_putNewSegsRoom SIS.Tree.liveCase_putNewSegFull SIS.Tree.deadCase_putLeafRoom
  SIS.Tree.deadCase_putLeafFull SIS.Tree.deadCase_putNewSeg1Room SIS.Tree.deadCase_putNewSegsRoom
  SIS.Tree.deadCase_putNewSegFull

end SIS.Tree
