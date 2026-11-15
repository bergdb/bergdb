/-
The heights' walk carried in the joint induction along a transaction, with TP7's
fill (bergdb 024-12, `hchk`; 024-22, step 4).

`hchk` (`OpDelChk2OK`) is the delete's checked copy at every reached delete. Two
of its checks, the upward delete's stop node and the take-back's parent being
segment leaves, hold by the fill at the delete's start (`stopLeaf_of_liveCounts`),
but in the top theorem's proof the fill at an operation's start comes from the
cases of the operations before it, whose fuel comes from the heights, whose walk
uses `hchk`: a cycle in the lemmas, though not in the transaction's order. This
file breaks it: one induction along the transaction carries `PutInv`, the ranges,
the fill and the heights' walk (`HtInv`) together (`jointHt_reached`). The fuel at
a state needs the heights at that state only, as a put takes nothing back
(`putKv_put_taken`, TakenPut.lean), and the cases of the delete with the merges are
restated with the heights' facts at their start given (`HtStartAt`, in place of
`OpHtDelOKUnder`).

So `hchk` is needed only at the deletes whose start has the fill, `PutInv`, the
ranges and the heights, at the induction's runs (`OpDelChk2OKL`):
`opDelChk2OK_of_chk2L` gives `OpDelChk2OK` from it and the other premises of the
top theorem, and `invGetScanOK_merges_chkL` is the top theorem with it.
-/
import SIS.Tree.LatestTop
import SIS.Tree.TakenPut

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! ## The premise -/

/-- `hchk` at the deletes of the runs of R whose start has `PutInv`, the walk's
ranges, TP7's fill and the heights' walk: the delete runs as its checked copy
(`putKvDelChk2`). -/
def OpDelChk2OKR (p : Params) (R : Struct BVal → Time → Prop) : Prop :=
  ∀ ts tx, Within p (ts ++ [tx]) → R (treeRun p ts) ts.length → ∀ z top,
    lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z →
    topOf p (ctxOf p ts).view z = .ok top →
    ∀ pre key post, tx.ops = pre ++ Op.del key :: post →
    ∀ r w, (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
    PutInv (ctxOf p ts) (viewOf (treeRun p ts)) w →
    RangeOrder (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey →
    LiveCounts p (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey →
    HtInv (htOracleOf p (treeRun p ts)) tx.base (ctxOf p ts) w →
    ∀ r' v, putKv (.del key) (ctxOf p ts) w = .ok (r', v) →
      putKvDelChk2 key (ctxOf p ts) w = .ok (r', v)

/-- `hchk` at the deletes of the induction's runs (TP4, P's tree, TP7's invariant
and the bound on dead klongs at the run) whose start has `PutInv`, the walk's
ranges, TP7's fill and the heights' walk. -/
def OpDelChk2OKL (p : Params) : Prop := OpDelChk2OKR p (RunTreeQ p (LatestQD p))

/-- `hchk` gives its narrowed form. -/
theorem opDelChk2OKL_of (p : Params) (h : OpDelChk2OK p) : OpDelChk2OKL p :=
  fun ts tx hw _ z top hz htop pre key post hs r w hpre _ _ _ _ r' v he =>
    h ts tx hw z top hz htop pre key post hs r w hpre r' v he

/-! ## The heights' facts at a state, from the heights' walk there -/

/-- The heights' facts at a state between operations (`htStart_reachedU`'s). -/
def HtStartAt (p : Params) (ts : List Tx) (tx : Tx) (w : W) : Prop :=
  ViewHtOK (htOracleOf p (treeRun p ts)) tx.base (ctxOf p ts) ∧
  ViewKlongsWf p (ctxOf p ts).view ∧
  BaseHeights (ctxOf p ts) (htOracleOf p (treeRun p ts)) (viewOf (treeRun p ts)) ∧
  (∀ y h, htOracleOf p (treeRun p ts) y h → h ≤ p.H) ∧
  Book tx.base (ctxOf p ts) w ∧ HtInv (htOracleOf p (treeRun p ts)) tx.base (ctxOf p ts) w ∧
  WriterKlongsWf w ∧ UntakenBound (p.fuel - 1) w

/-- Every node an operation takes back has a height below the fuel, from the
deletes' (`TakeBelowFuelDelOK`): a put takes nothing back (`putKv_put_taken`),
with no heights' walk. -/
theorem takeBelowFuelOK_of_del (p : Params) (hdel : TakeBelowFuelDelOK p) :
    ∀ ts tx, Within p (ts ++ [tx]) → ∀ z top,
      lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z →
      topOf p (ctxOf p ts).view z = .ok top →
      ∀ pre op post, tx.ops = pre ++ op :: post →
      ∀ r w, (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
      ∀ a v, putKv op (ctxOf p ts) w = .ok (a, v) →
      ∀ x g h, (x, g, h) ∈ w.gh → w.taken.contains x = false → v.taken.contains x = true →
        h < p.fuel := by
  intro ts tx hw z top hz htop pre op post hsplit r w hpre a v he x g h hm hx hv
  cases op with
  | del key => exact hdel ts tx hw z top hz htop pre key post hsplit r w hpre a v he x g h hm hx hv
  | put key hv0 =>
    exfalso
    rw [putKv_put_taken key hv0 _ w a v he, hx] at hv
    cases hv

set_option maxHeartbeats 1600000 in
/-- `htStart_reachedU` with the heights' walk at the state given: no walk of the
deletes before it, and none after it. -/
theorem htStart_of_ht (p : Params) (R : Struct BVal → Time → Prop)
    (hRL : ∀ P t, R P t → RunLinksOK p P t) (hRK : ∀ P t, R P t → KindsAllOK p P)
    (hRH : ∀ P t, R P t → HeightAllOK p P t)
    (hdel : TakeBelowFuelDelOK p) (ts : List Tx) (tx : Tx) (hw : Within p (ts ++ [tx]))
    (hr : R (treeRun p ts) ts.length) (z : NodeId) (top : Top)
    (hz : lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z)
    (htop : topOf p (ctxOf p ts).view z = .ok top) (pre post : List Op)
    (hsplit : tx.ops = pre ++ post) (r : List Bool) (w : W)
    (hpre : (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w))
    (hi : HtInv (htOracleOf p (treeRun p ts)) tx.base (ctxOf p ts) w) :
    HtStartAt p ts tx w := by
  have htb := takeBelowFuelOK_of_del p hdel ts tx hw z top hz htop
  have hR := hRL _ _ hr
  have hK := hRK _ _ hr
  have hA := hRH _ _ hr
  have hvo := viewHtOK_of_run p ts tx hw hR hK hA
  have hbk := putBook_reached p ts tx hw hR z top htop pre r w hpre
  have hB := putBase_of_run p ts tx hw hR
  have hub : ∀ x g h, (x, g, h) ∈ w.gh → w.taken.contains x = false → h < p.fuel := by
    intro x g h hm hx
    rcases Nat.lt_or_ge h p.fuel with hlt | hge
    · exact hlt
    exfalso
    have hHh : p.H < h := by have := fuel_gt_H p; omega
    have hmk : HeightMarkedPred p w.gh w.outside := by
      letI := heightMarkedFields
      exact fields_ops pre (ctxOf p ts) (wInit tx top)
        (by change HeightMarkedPred p [] []; simp [HeightMarkedPred]) r w hpre
    have hout := hmk x g h hm hHh
    obtain ⟨bs, wE, he⟩ := execW_success_of_within_snoc p ts tx hw
    unfold execW runOps runOpsFrom at he
    rw [hz] at he
    simp only at he
    have htop' : topOf p (rootless (view (treeSpec p) (treeRun p ts) ts.length)) z = .ok top := htop
    rw [htop'] at he
    simp only at he
    have hrun := boundsOK_ok p _ bs wE he
    have hbnd : ∀ q ∈ wE.outside, wE.taken.contains q.1 = true := by
      unfold boundsOK at he
      rw [hrun] at he
      simp only at he
      split at he
      · cases he
      · rename_i hf
        intro q hq
        have := List.find?_eq_none.mp hf q hq
        simpa using this
    have hrun' : ((pre ++ post).mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (bs, wE) := by
      rw [← hsplit]; exact hrun
    obtain ⟨r2, hpost⟩ := mapM_split_run (ctxOf p ts) (wInit tx top) pre post r w bs wE hpre hrun'
    have houtE : (x, g, h) ∈ wE.outside := by
      letI := outsideHasFields (x, g, h)
      exact fields_ops post (ctxOf p ts) w hout r2 wE hpost
    have htE := hbnd _ houtE
    obtain ⟨pre', op, post', r', u, a, v, hs', hp', ho', hu, hv, rest, r3, hrest⟩ :=
      taken_by_op (ctxOf p ts) (wInit tx top) tx.ops x post pre hsplit r w r2 wE hpre hpost hx htE
    have hmu : (x, g, h) ∈ u.gh := by
      letI := ghHasFields (x, g, h)
      exact fields_ops rest (ctxOf p ts) w hm r3 u hrest
    have := htb pre' op post' hs' r' u hp' a v ho' x g h hmu hu hv
    omega
  have htimes : StructTimesLE (treeRun p ts) ts.length := treeRun_timesLE p ts
  have hbase := baseHeights_of p (treeRun p ts) ts.length (ctxOf p ts) rfl
    (by simp [ctxOf]) htimes hR.1 hK hA
  refine ⟨hvo, hB.wf, hbase, ?_, hbk.book, hi, hbk.klongs, fun x g h hm hx => ?_⟩
  · rintro y h ⟨ny, _, _, _, hny⟩
    exact hny ▸ heightOf_le p ny.level
  · have := hub x g h hm hx; omega

/-- The fuel at a state from the heights' facts there (as
`txSegFitsOK_of_takeBelowDelRHU`). -/
theorem segFits_of_htStart (p : Params) (ts : List Tx) (tx : Tx) (w : W)
    (h : HtStartAt p ts tx w) :
    SegFits (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) (p.fuel - 1) w.top.rootKey := by
  obtain ⟨hvo, -, hbase, hHb, hbk, hi, -, hub⟩ := h
  refine segFits_of_heightsU hbk hi.cache hvo.heights _ hbase (p.fuel - 1) _ ?_
  intro x n hn h hh
  rcases hh with ⟨g, hm⟩ | hh
  · exact hub x g h hm (wNode_cases _ _ _ _ _ hn).1
  · have := hHb x h hh
    have := fuel_gt_H p
    omega

/-! ## The delete with the merges, the heights' facts at its start given -/

/-- `DelStepsCaseQd` with the heights' facts at the operation's start given. -/
def DelStepsCaseQdH (p : Params) (R : Struct BVal → Time → Prop)
    (P : Ctx → View BVal → W → Op → Prop) : Prop :=
  ∀ ts tx, Within p (ts ++ [tx]) → R (treeRun p ts) ts.length → ∀ z top,
    lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z →
    topOf p (ctxOf p ts).view z = .ok top →
    ∀ pre op post, tx.ops = pre ++ op :: post →
    ∀ r w, (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
    HtStartAt p ts tx w →
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

/-- `DelStepsQdL` with the heights' facts at the operation's start given. -/
def DelStepsQdLH (p : Params) (R : Struct BVal → Time → Prop) : Prop :=
  DelStepsCaseQdH p R (fun c base w op => (∃ key, op = .del key ∧ c.p.merges = true) ∧
    LiveCounts c.p (wNode c.p base w) c.i w.top.rootKey)

/-- `OpCaseOK` with the heights' facts at the operation's start given. -/
def OpCaseOKH (p : Params) (R : Struct BVal → Time → Prop) (Q : List Tx → Op → W → W → Prop)
    (P : Ctx → View BVal → W → Op → Prop) : Prop :=
  ∀ ts tx, Within p (ts ++ [tx]) → R (treeRun p ts) ts.length → ∀ z top,
    lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z →
    topOf p (ctxOf p ts).view z = .ok top →
    ∀ pre op post, tx.ops = pre ++ op :: post →
    ∀ r w, (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
    HtStartAt p ts tx w →
    PutInv (ctxOf p ts) (viewOf (treeRun p ts)) w →
    RangeOrder (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey →
    P (ctxOf p ts) (viewOf (treeRun p ts)) w op →
    WriterWP (putKv op) (ctxOf p ts) w (fun _ w' => Q ts op w w')

theorem delStepsCaseQdH_emptyCasc (p : Params) (R : Struct BVal → Time → Prop) (hM : 2 ≤ p.M)
    (hsa2 : 2 ≤ p.splitAbove)
    (hRL : ∀ P t, R P t → RunLinksOK p P t)
    (hRP : ∀ P t, R P t → PointersOK P) (hRK : ∀ P t, R P t → KindsAllOK p P)
    (hU : ∀ ts, UpUnlinkTreeOK (ctxOf p ts) (viewOf (treeRun p ts)))
    (hHL : ∀ ts, UpHolderLiveRunOK (ctxOf p ts) (viewOf (treeRun p ts)))
    : DelStepsCaseQdH p R DelEmptyCascML := by
  intro ts tx hw hr z top hz htop ops op post hops r w hpre hH hI hRO hF key hop hPcL hA hMU hCR
  obtain ⟨hPc, hLCw⟩ := hPcL
  obtain ⟨pre, cv, L0, n0, hop', hm, hK, hne0, hall0, P0, hP0, hX0, hl0, _⟩ := hPc
  subst hop'
  cases hop
  obtain ⟨hvo, hkw, hbase, hHb, _, hhi, hwfw, hub⟩ := hH
  have hkey : keyWf (pre ++ [cv]) = true := within_op_keyWf p ts tx hw ops _ post hops
  obtain ⟨rk, hrk, _⟩ := keyLeaf_rk hK
  have hB := putBase_of_run p ts tx hw (hRL _ _ hr)
  have hbook := putBook_reached p ts tx hw (hRL _ _ hr) z top htop ops r w hpre
  have hICE := innerChildren_reachedR p hM ts tx (hRP _ _ hr) (hRK _ _ hr) hw top ops (.del (pre ++ [cv]) :: post) hops r w hpre
    (fun x hx => hI.untaken x (tReach_reachS _ _ _ _ hx))
  obtain ⟨hv, hk, hb0, hi0⟩ := kd_contextR p hM ts tx (hRP _ _ hr) (hRK _ _ hr) hw top ops (.del (pre ++ [cv]) :: post) hops r w hpre
  have hwts : Within p ts := by
    have := within_take p (ts ++ [tx]) hw ts.length
    simpa using this
  have hKall := hRK _ _ hr
  have hICEk : ICEFromKinds (ctxOf p ts) (viewOf (treeRun p ts)) (kindOracleOf p (treeRun p ts)) tx.base :=
    fun v hb hi hun => innerChildren_of_kinds p (treeRun p ts) tx.base (ctxOf p ts) v rfl hKall
      (hRP _ _ hr) hb hi.cache hun
  have hLr : L0 ≠ w.top.rootKey := by
    intro he
    obtain ⟨j, hj⟩ : ∃ j, P0.length = j + 1 := ⟨P0.length - 1, by omega⟩
    have hPL := LinkedFrom.pathLen _ _ _ P0 hP0
    have h1 := hPL P0.length (Nat.le_refl _)
    rw [hX0, he] at h1
    have h0 : PathLen (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey w.top.rootKey 0 :=
      PathLen.root
    have := PathLen.depth_unique hI.tree _ _ _ h1 h0
    omega
  refine writerWP_del_emptyAnyMKLHG (ctxOf p ts) _ (viewCoherent_ctxOf p ts) pre cv rk w tx.base top hB hbook
    _ tx.base hv hk hb0 hi0 hI hRO hF hICE hkey hrk (keyLeaf_all2 hK hrk _ ⟨hne0, hall0, hLr⟩)
    _ (upCascOKHG_of _ _ _ _ _ (hU ts) (hHL ts)
      (upCascFitsOKR_of _ _ _ _ _ hvo hbase hHb (by simp [ctxOf]))) hLCw hvo hkw hhi hwfw hub
    (by simpa [ctxOf] using hsa2) hICEk hm (by simp [ctxOf]) hA hMU hCR
    (QdW p ts) (fun v hv' => qdW_fresh p ts v hv') (fun v hv' => ⟨hv'.1.1, hv'.1.2.2.1⟩)

theorem delStepsCaseQdH_fullH (p : Params) (R : Struct BVal → Time → Prop) (hM : 2 ≤ p.M)
    (hsa2 : 2 ≤ p.splitAbove)
    (hRL : ∀ P t, R P t → RunLinksOK p P t)
    (hRP : ∀ P t, R P t → PointersOK P)
    (hRK : ∀ P t, R P t → KindsAllOK p P) (hRH : ∀ P t, R P t → HeightAllOK p P t)
    (hRoot : ∀ ts, DelFullRootStepOK (ctxOf p ts) (viewOf (treeRun p ts))) :
    DelStepsCaseQdH p R DelFullM := by
  intro ts tx hw hr z top hz htop ops op post hops r w hpre hH hI hRO hF key hop hPc hA _ _
  obtain ⟨pre, cv, L0, n0, hop', _, hK, hne0, hkeep0, hfull0⟩ := hPc
  subst hop'
  cases hop
  have hkey : keyWf (pre ++ [cv]) = true := within_op_keyWf p ts tx hw ops _ post hops
  obtain ⟨rk, hrk, _⟩ := keyLeaf_rk hK
  have hB := putBase_of_run p ts tx hw (hRL _ _ hr)
  have hbook := putBook_reached p ts tx hw (hRL _ _ hr) z top htop ops r w hpre
  obtain ⟨hv, hk, hb0, hi0⟩ := kd_contextR p hM ts tx (hRP _ _ hr) (hRK _ _ hr) hw top ops (.del (pre ++ [cv]) :: post) hops r w hpre
  have hwts : Within p ts := by
    have := within_take p (ts ++ [tx]) hw ts.length
    simpa using this
  have hKall := hRK _ _ hr
  have hICEk : ICEFromKinds (ctxOf p ts) (viewOf (treeRun p ts)) (kindOracleOf p (treeRun p ts)) tx.base :=
    fun v hb hi hun => innerChildren_of_kinds p (treeRun p ts) tx.base (ctxOf p ts) v rfl hKall
      (hRP _ _ hr) hb hi.cache hun
  have hJ0 : KdJ (ctxOf p ts) tx.base top (kindOracleOf p (treeRun p ts)) tx.base w := ⟨hbook, hb0, hi0⟩
  obtain ⟨hvo, hkw, _, _, _, hhi, hwfw, hub⟩ := hH
  refine writerWP_del_toLeafMKH (ctxOf p ts) _ (viewCoherent_ctxOf p ts) pre cv rk w
    (KdHtJ (ctxOf p ts) tx.base top (kindOracleOf p (treeRun p ts)) tx.base (htOracleOf p (treeRun p ts)))
    (fun s f x v hJ hx => kdhtJ_descendLte _ top hB _ tx.base hv hk hvo hkw s f x v hJ hx)
    (fun s fd L n v hJ hL hlk hleaf hfd => kdhtJ_pathAdd _ top hB _ tx.base hv hvo s fd L n v hJ hL hlk hleaf hfd)
    (kdhtJ_start _ top hB _ tx.base hv hvo w hJ0 hhi hwfw hub) hrk (hI.pathUntaken _) hI.wf _ ?_ ?_
  · exact fun v hv' => qdW_fresh p ts v hv'
  · intro L n P w3 hL hn hnl hr03 hJ3 hlk3 hp3' hlinkP hXD hlkX
    obtain ⟨hne, hkeep, hfull⟩ := keyLeaf_all2 hK hrk
      (fun _ m => bitsUnion m.lastBitmap (m.bitsOf cv) ≠ m.lastBitmap ∧
        m.allKeysIn (bitsUnion m.lastBitmap (m.bitsOf cv)) = false ∧ ¬ DelRoom (ctxOf p ts) cv m)
      ⟨hne0, hkeep0, hfull0⟩ L n hL hn hnl
    refine writerWP_deleteUpward_full (ctxOf p ts) L n P.length cv (pre ++ [cv]) w3 hlk3 hne hkeep
      (fun v => DelInv (ctxOf p ts) (viewOf (treeRun p ts)) w (pre ++ [cv]) (p.fuel + 1)
        (kindOracleOf p (treeRun p ts)) tx.base v) _
      (writerWP_appendDeleteKlong_full_delH (ctxOf p ts) _ (viewCoherent_ctxOf p ts) _ tx.base (hRoot ts) _
        (delFullFitsOKR_run p ts tx hw (hRL _ _ hr) (hRK _ _ hr) (hRH _ _ hr))
        hsa2 hv hk hICEk w pre cv rk tx.base top hB hI hRO hF hkey hrk L n P w3 hL hn hnl hne hfull
        hr03 hJ3.1 hJ3.2 hp3' hlinkP hXD hlkX) ?_
    intro g h v hv'
    exact writerWP_mono (hA g h v hv') (fun _ v' hv'' => ⟨hv''.1.1, hv''.1.2.2.1⟩)

theorem delStepsQdLH_of_openR (p : Params) (R : Struct BVal → Time → Prop) (hM : 2 ≤ p.M)
    (hsa2 : 2 ≤ p.splitAbove)
    (hRL : ∀ P t, R P t → RunLinksOK p P t)
    (hRP : ∀ P t, R P t → PointersOK P) (hRK : ∀ P t, R P t → KindsAllOK p P)
    (hRH : ∀ P t, R P t → HeightAllOK p P t)
    (hU : ∀ ts, UpUnlinkTreeOK (ctxOf p ts) (viewOf (treeRun p ts)))
    (hHL : ∀ ts, UpHolderLiveRunOK (ctxOf p ts) (viewOf (treeRun p ts))):
    DelStepsQdLH p R := by
  intro ts tx hw hr z top hz htop pre op post hops r w hpre hH hI hRO hF key hop hmL hA hMU hCR
  obtain ⟨⟨key', hop', hm'⟩, hLCw⟩ := hmL
  rw [hop] at hop'
  cases hop'
  rcases delMerge_cover (ctxOf p ts) (viewOf (treeRun p ts)) w key hm' with h | h | h | h | h
  · exact delStepsCaseQd_noLeaf p R ts tx hw hr z top hz htop pre op post hops r w hpre hI hRO hF key hop
      (hop ▸ h) hA hMU hCR
  · exact delStepsCaseQd_noop p R hRL ts tx hw hr z top hz htop pre op post hops r w hpre hI hRO hF key hop
      (hop ▸ h) hA hMU hCR
  · rcases delEmptyM_split _ _ _ _ h with h1 | h1
    · exact delStepsCaseQd_emptyRoom p R hM hRL hRP hRK ts tx hw hr z top hz htop pre op post hops r w hpre
        hI hRO hF key hop (hop ▸ h1) hA hMU hCR
    · rcases delEmptyOther_split _ _ _ _ h1 with h2 | h2
      · exact delStepsCaseQd_emptyRoot p R hM hsa2 hRL hRP hRK ts tx hw hr z top hz htop pre op post hops r w
          hpre hI hRO hF key hop (hop ▸ h2) hA hMU hCR
      · exact delStepsCaseQdH_emptyCasc p R hM hsa2 hRL hRP hRK hU hHL
          ts tx hw hr z top hz htop pre op post hops r w hpre hH hI hRO hF key hop (hop ▸ ⟨h2, hLCw⟩) hA hMU hCR
  · exact delStepsCaseQd_room p R hM hRL hRP hRK ts tx hw hr z top hz htop pre op post hops r w hpre hI hRO hF
      key hop (hop ▸ h) hA hMU hCR
  · exact delStepsCaseQdH_fullH p R hM hsa2 hRL hRP hRK hRH (fun ts => delFullRootStepOK_ctx p ts)
      ts tx hw hr z top hz htop pre op post hops r w hpre hH hI hRO hF key hop (hop ▸ h) hA hMU hCR

theorem opCaseOKH_qdW_delMergeRL (p : Params) (R : Struct BVal → Time → Prop) (hS : DelStepsQdLH p R)
    (hM : ∀ ts, MergeStepOK (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1))
    (hC : ∀ ts, CollapseStepOK (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1))
    (hsa2 : 2 ≤ p.splitAbove) (hcap : 1 ≤ p.mergeMax)
    (hRP : ∀ P t, R P t → PointersOK P) (hRK : ∀ P t, R P t → KindsAllOK p P) :
    OpCaseOKH p R (fun ts _ _ w' => QdW p ts w') DelMergeCaseL := by
  have hf2 : 2 ≤ p.fuel + 1 := by unfold Params.fuel; omega
  intro ts tx hw hr z top hz htop pre op post hops r w hpre hH hI hRO hP
  obtain ⟨⟨key, hop, hmerges⟩, hLCw⟩ := hP
  have hF0 := segFits_of_htStart p ts tx w hH
  have hwts : Within p ts := by
    have := within_take p (ts ++ [tx]) hw ts.length
    simpa using this
  have hfresh : ∀ q ∈ treeRun p ts, q.1 < tx.base := by
    have := (hw.2 ts.length (by simp)).1
    simpa using this
  have hK := hRK _ _ hr
  have hv : ViewIdsBelow tx.base (ctxOf p ts).view :=
    viewIdsBelow_rootless _ _ (viewIdsBelow_view p (treeRun p ts) ts.length tx.base hfresh)
  have hk : ViewKinds (kindOracleOf p (treeRun p ts)) tx.base (ctxOf p ts) :=
    viewKinds_of p (treeRun p ts) ts.length tx.base hfresh (treeRun_timesLE p ts) (hRP _ _ hr) hK
  have hICEk : ICEFromKinds (ctxOf p ts) (viewOf (treeRun p ts)) (kindOracleOf p (treeRun p ts)) tx.base :=
    fun v hb hi hun => innerChildren_of_kinds p (treeRun p ts) tx.base (ctxOf p ts) v rfl hK
      (hRP _ _ hr) hb hi.cache hun
  exact hS ts tx hw hr z top hz htop pre op post hops r w hpre hH hI hRO hF0 key hop ⟨⟨key, hop, hmerges⟩, hLCw⟩
    (fun g h v hv' => writerWP_afterDelete_del key g h (ctxOf p ts) _ (viewCoherent_ctxOf p ts)
      (p.fuel + 1) hf2 (hM ts) (hC ts) _ _ hv hk hICEk hsa2 hcap w key v hv')
    (fun g h merged v hv' => writerWP_mergeUp_del key g (ctxOf p ts) _ (viewCoherent_ctxOf p ts)
      (p.fuel + 1) hf2 (hM ts) _ _ hv hk hICEk hsa2 hcap w key p.fuel h merged v hv')
    (fun seg v hv' => writerWP_collapseRoot_del key seg (ctxOf p ts) _ (viewCoherent_ctxOf p ts)
      (p.fuel + 1) hf2 (hC ts) w key _ _ hv hk hICEk hsa2 v hv')

theorem opCaseOKH_treeInvRange_delMergeRL (p : Params) (R : Struct BVal → Time → Prop) (hS : DelStepsQdLH p R)
    (hM : ∀ ts, MergeStepOK (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1))
    (hC : ∀ ts, CollapseStepOK (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1))
    (hsa2 : 2 ≤ p.splitAbove) (hcap : 1 ≤ p.mergeMax)
    (hRP : ∀ P t, R P t → PointersOK P) (hRK : ∀ P t, R P t → KindsAllOK p P) :
    OpCaseOKH p R (QTree p) DelMergeCaseL ∧ OpCaseOKH p R (QPutInv p) DelMergeCaseL ∧
      OpCaseOKH p R (QRange p) DelMergeCaseL := by
  have h := opCaseOKH_qdW_delMergeRL p R hS hM hC hsa2 hcap hRP hRK
  refine ⟨?_, ?_, ?_⟩
  · intro ts tx hw hr z top hz htop pre op post hops r w hpre hH hI hRO hP
    exact writerWP_mono (h ts tx hw hr z top hz htop pre op post hops r w hpre hH hI hRO hP)
      (fun _ w' hq => hq.1.tree)
  · intro ts tx hw hr z top hz htop pre op post hops r w hpre hH hI hRO hP
    exact writerWP_mono (h ts tx hw hr z top hz htop pre op post hops r w hpre hH hI hRO hP)
      (fun _ w' hq _ => hq.1)
  · intro ts tx hw hr z top hz htop pre op post hops r w hpre hH hI hRO hP
    exact writerWP_mono (h ts tx hw hr z top hz htop pre op post hops r w hpre hH hI hRO hP)
      (fun _ w' hq _ => hq.2)

/-! ## The joint induction along a transaction -/

/-- A put's post. -/
def QPut (Q : List Tx → Op → W → W → Prop) : List Tx → Op → W → W → Prop :=
  fun ts op w w' => (∀ key, op ≠ .del key) → Q ts op w w'

/-- A case at every put from the put cases (1) to (3): a delete makes `QPut`
void. -/
theorem opCaseOK_put_of_cases (p : Params) (R : Struct BVal → Time → Prop)
    (Q : List Tx → Op → W → W → Prop) (hm : p.merges = true)
    (c1 : OpCaseOK p R Q PutLeafRoomCase) (c2 : OpCaseOK p R Q PutLeafFullCase)
    (c3 : OpCaseOK p R Q PutNewSegCase) : OpCaseOK p R (QPut Q) AnyOp := by
  have lift : ∀ C, OpCaseOK p R Q C → OpCaseOK p R (QPut Q) C :=
    fun C h ts tx hw hr z top hz htop pre op post hs r w hpre hI hRO hC =>
      writerWP_mono (h ts tx hw hr z top hz htop pre op post hs r w hpre hI hRO hC)
        (fun _ _ hq _ => hq)
  have c4 : OpCaseOK p R (QPut Q) DelMergeCase := by
    intro ts tx hw hr z top hz htop pre op post hs r w hpre hI hRO hC
    obtain ⟨key, hop, _⟩ := hC
    intro _ _ _ hne
    exact absurd hop (hne key)
  exact opCaseOK_of_cases_merges p R (QPut Q) hm (lift _ c1) (lift _ c2) (lift _ c3) c4

set_option maxHeartbeats 1600000 in
/-- `PutInv`, the walk's ranges, TP7's fill and the heights' walk at every state
that a prefix of a transaction's operations reaches, at the runs of R: the cases
of the puts as they are, those of the delete with the merges with the heights'
facts at its start, and the delete's checked copy (`OpDelChk2OKR`) where the fill
holds at its start. -/
theorem jointHt_reached (p : Params) (R : Struct BVal → Time → Prop) (hm : p.merges = true)
    (hM : 2 ≤ p.M)
    (hRL : ∀ P t, R P t → RunLinksOK p P t) (hRT : ∀ P t, R P t → TreeAt p P t)
    (hRI : ∀ P t, R P t → InvOK p P t) (hRP : ∀ P t, R P t → PointersOK P)
    (hRK : ∀ P t, R P t → KindsAllOK p P) (hRH : ∀ P t, R P t → HeightAllOK p P t)
    (hdel : TakeBelowFuelDelOK p)
    (hTp : OpCaseOK p R (QPut (QTree p)) AnyOp) (hPp : OpCaseOK p R (QPut (QPutInv p)) AnyOp)
    (hOp : OpCaseOK p R (QPut (QRange p)) AnyOp)
    (hTd : OpCaseOKH p R (QTree p) DelMergeCaseL) (hPd : OpCaseOKH p R (QPutInv p) DelMergeCaseL)
    (hOd : OpCaseOKH p R (QRange p) DelMergeCaseL)
    (hLv : OpCaseOK p R (QLive p) AnyOp) (hchk : OpDelChk2OKR p R)
    (ts : List Tx) (tx : Tx) (hw : Within p (ts ++ [tx])) (hr : R (treeRun p ts) ts.length)
    (z : NodeId) (top : Top)
    (hz : lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z)
    (htop : topOf p (ctxOf p ts).view z = .ok top) :
    ∀ pre post, tx.ops = pre ++ post → ∀ r w,
      (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
      PutInv (ctxOf p ts) (viewOf (treeRun p ts)) w ∧
      RangeOrder (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey ∧
      LiveCounts p (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey ∧
      HtInv (htOracleOf p (treeRun p ts)) tx.base (ctxOf p ts) w := by
  intro pre
  suffices hk : ∀ k, ∀ pre : List Op, pre.length = k → ∀ post, tx.ops = pre ++ post → ∀ r w,
      (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
      PutInv (ctxOf p ts) (viewOf (treeRun p ts)) w ∧
      RangeOrder (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey ∧
      LiveCounts p (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey ∧
      HtInv (htOracleOf p (treeRun p ts)) tx.base (ctxOf p ts) w
    from hk pre.length pre rfl
  have hR := hRL _ _ hr
  have hvo := viewHtOK_of_run p ts tx hw hR (hRK _ _ hr) (hRH _ _ hr)
  intro k
  induction k with
  | zero =>
    intro pre hl _ _ r w h
    have hnil : pre = [] := List.eq_nil_of_length_eq_zero hl
    subst hnil
    simp only [List.mapM_nil, pure, ReaderT.pure, StateT.pure, Except.pure, Except.ok.injEq,
      Prod.mk.injEq] at h
    rw [← h.2]
    exact ⟨putInv_init p ts tx hw hR (hRT _ _ hr) (hRI _ _ hr) z top hz htop,
      rangeOrder_init p ts tx (hRI _ _ hr) z top hz htop,
      liveCounts_init p ts tx (hRI _ _ hr) z top hz htop, htInv_start _ _ _ top⟩
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
          obtain ⟨hI1, hR1, hL1, hH1⟩ := ih pre' hl' (op :: post) hsplit' r1 w1 h1
          have hbk := putBook_reached p ts tx hw hR z top htop pre' r1 w1 h1
          have hB := putBase_of_run p ts tx hw hR
          rw [← h.2]
          cases op with
          | put key hv0 =>
            have hne : ∀ key', Op.put key hv0 ≠ .del key' := fun _ he => by cases he
            have hT2 : WriterTreeOK p (treeRun p ts) (ts.length + 1) w2 :=
              hTp ts tx hw hr z top hz htop pre' _ post hsplit' r1 w1 h1 hI1 hR1 trivial a w2 h2 hne
            have hI2 := hPp ts tx hw hr z top hz htop pre' _ post hsplit' r1 w1 h1 hI1 hR1 trivial a w2
              h2 hne hT2
            have hR2 := hOp ts tx hw hr z top hz htop pre' _ post hsplit' r1 w1 h1 hI1 hR1 trivial a w2
              h2 hne hT2
            have hL2 := hLv ts tx hw hr z top hz htop pre' _ post hsplit' r1 w1 h1 hI1 hR1 trivial a w2
              h2 hT2 hL1
            have hH2 := (ht_putKv_put tx.base (appendFrameOK tx.base) key hv0 (ctxOf p ts) w1 hvo
              (by simp [ctxOf]) hbk.book hH1 hM hB.wf hbk.klongs a w2 h2).2.1
            exact ⟨hI2, hR2, hL2, hH2⟩
          | del key =>
            have hHS := htStart_of_ht p R hRL hRK hRH hdel ts tx hw hr z top hz htop pre'
              (Op.del key :: post) hsplit' r1 w1 h1 hH1
            have hC : DelMergeCaseL (ctxOf p ts) (viewOf (treeRun p ts)) w1 (Op.del key) :=
              ⟨⟨key, rfl, hm⟩, hL1⟩
            have hT2 : WriterTreeOK p (treeRun p ts) (ts.length + 1) w2 :=
              hTd ts tx hw hr z top hz htop pre' _ post hsplit' r1 w1 h1 hHS hI1 hR1 hC a w2 h2
            have hI2 := hPd ts tx hw hr z top hz htop pre' _ post hsplit' r1 w1 h1 hHS hI1 hR1 hC a w2
              h2 hT2
            have hR2 := hOd ts tx hw hr z top hz htop pre' _ post hsplit' r1 w1 h1 hHS hI1 hR1 hC a w2
              h2 hT2
            have hL2 := hLv ts tx hw hr z top hz htop pre' _ post hsplit' r1 w1 h1 hI1 hR1 trivial a w2
              h2 hT2 hL1
            have hc2 := hchk ts tx hw hr z top hz htop pre' key post hsplit' r1 w1 h1 hI1 hR1 hL1 hH1
              a w2 h2
            obtain ⟨-, hk, -, hki⟩ := kd_contextR p hM ts tx (hRP _ _ hr) (hRK _ _ hr) hw top pre'
              (Op.del key :: post) hsplit' r1 w1 h1
            have hH2 := (ht_putKvDelChk2 tx.base key (ctxOf p ts) w1 hvo (by simp [ctxOf])
              hHS.2.1 hbk.book hH1 hbk.klongs hk hki (by simpa [ctxOf] using hM) a w2 hc2).2.1
            exact ⟨hI2, hR2, hL2, hH2⟩

/-- The delete side of the heights' walk at the runs of R, from the joint
induction and the checked copy where the fill holds. -/
theorem opHtDelOKUnder_of_joint (p : Params) (R : Struct BVal → Time → Prop) (hm : p.merges = true)
    (hM : 2 ≤ p.M)
    (hRL : ∀ P t, R P t → RunLinksOK p P t) (hRT : ∀ P t, R P t → TreeAt p P t)
    (hRI : ∀ P t, R P t → InvOK p P t) (hRP : ∀ P t, R P t → PointersOK P)
    (hRK : ∀ P t, R P t → KindsAllOK p P) (hRH : ∀ P t, R P t → HeightAllOK p P t)
    (hdel : TakeBelowFuelDelOK p)
    (hTp : OpCaseOK p R (QPut (QTree p)) AnyOp) (hPp : OpCaseOK p R (QPut (QPutInv p)) AnyOp)
    (hOp : OpCaseOK p R (QPut (QRange p)) AnyOp)
    (hTd : OpCaseOKH p R (QTree p) DelMergeCaseL) (hPd : OpCaseOKH p R (QPutInv p) DelMergeCaseL)
    (hOd : OpCaseOKH p R (QRange p) DelMergeCaseL)
    (hLv : OpCaseOK p R (QLive p) AnyOp) (hchk : OpDelChk2OKR p R) : OpHtDelOKUnder p R := by
  intro ts tx hw hr z top hz htop pre key post hsplit r w hpre hvo hkw hb hwf hi r' v he
  obtain ⟨hI, hRo, hL, _⟩ := jointHt_reached p R hm hM hRL hRT hRI hRP hRK hRH hdel hTp hPp hOp
    hTd hPd hOd hLv hchk ts tx hw hr z top hz htop pre (Op.del key :: post) hsplit r w hpre
  have hc := hchk ts tx hw hr z top hz htop pre key post hsplit r w hpre hI hRo hL hi r' v he
  obtain ⟨-, hk, -, hki⟩ := kd_contextR p hM ts tx (hRP _ _ hr) (hRK _ _ hr) hw top pre
    (Op.del key :: post) hsplit r w hpre
  exact (ht_putKvDelChk2 tx.base key (ctxOf p ts) w hvo (by simp [ctxOf]) hkw hb hi hwf hk hki
    (by simpa [ctxOf] using hM) r' v hc).2.1

/-! ## `hchk` from its narrowed form -/

set_option maxHeartbeats 1600000 in
/-- `hchk` (`OpDelChk2OK`) from its narrowed form `OpDelChk2OKL` and the other
premises of the top theorem: the induction of `invGetScanOK_merges` with the
delete side of the heights' walk from the joint induction (`jointHt_reached`,
`opHtDelOKUnder_of_joint`), and then the joint induction at every run within
reach. -/
theorem opDelChk2OK_of_chk2L (p : Params) (hp : MergeParamsOK p)
    (hth : 2 ≤ p.theta ∨ p.theta = 0)
    (hchkL : OpDelChk2OKL p)
    (htb : TakeBelowFuelDelOK p)
    (d4 : OpCaseOK p (RunOK p) (QDead p) DelMergeDOpenCase)
    (l4 : OpCaseOK p (RunOK p) (QLive p) DelMergeOpenCase)
    (hU : ∀ ts, UpUnlinkTreeOK (ctxOf p ts) (viewOf (treeRun p ts)))
    (hHL : ∀ ts, UpHolderLiveRunOK (ctxOf p ts) (viewOf (treeRun p ts)))
    (hMSF : ∀ ts, MergeFitsOK (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1))
    (hCoF : ∀ ts, CollapseFitsOK (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1))
    (hCoU : ∀ ts, CollapseUnlinkAllOK (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1))
    (hMF : StateOK p (RunOK p) (fun _ tx w => ∀ x o, w.madeFor.lookup x = some o → o < tx.base)) :
    OpDelChk2OK p := by
  have hp' := hp
  unfold MergeParamsOK at hp'
  have hM := mergeParamsOK_M p hp
  have hm : p.merges = true := by
    unfold Params.merges; simp only [decide_eq_true_eq]; omega
  have hsa : 2 ≤ p.splitAbove := by omega
  have hcap : 1 ≤ p.mergeMax := by omega
  have hRL : ∀ P t, RunOK p P t → RunLinksOK p P t := fun _ _ h => h.1
  have hMS : ∀ ts, MergeStepOK (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1) :=
    fun ts => mergeStepOK_of_segFits (ctxOf p ts) _ _ (Nat.succ_pos _) hcap hsa (hMSF ts)
  have hCo : ∀ ts, CollapseStepOK (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1) :=
    fun ts => ⟨hCoF ts, hCoU ts⟩
  have hR : ∀ P t, RunTreeQ p (LatestQD p) P t → RunOK p P t := runOK_of_runTreeQD p
  have hRL' : ∀ P t, RunTreeQ p (LatestQD p) P t → RunLinksOK p P t := fun _ _ h => h.1
  have hRT' : ∀ P t, RunTreeQ p (LatestQD p) P t → TreeAt p P t := fun _ _ h => h.2.1
  have hRI' : ∀ P t, RunTreeQ p (LatestQD p) P t → InvOK p P t := fun _ _ h => h.2.2.1.1
  have hRP' : ∀ P t, RunTreeQ p (LatestQD p) P t → PointersOK P := fun _ _ h => h.1.1
  have hRK' : ∀ P t, RunTreeQ p (LatestQD p) P t → KindsAllOK p P := fun _ _ h => h.2.2.1.2.2.1
  have hRH' : ∀ P t, RunTreeQ p (LatestQD p) P t → HeightAllOK p P t :=
    fun _ _ h => h.2.2.1.2.2.2.1
  have l4' := opCaseOK_anti p _ _ hR _ _
    (liveCase_delMerge_of_rest p (RunOK p) hRL
      (opCaseOK_of_open p (RunOK p) (QLive p) (keptByReads_live p) DelMergeRestCase l4))
  -- the joint induction's cases: the puts' as they are, the delete's with the heights at its start
  have hLv := opCaseOK_of_cases_merges p _ _ hm (liveCase_putLeafRoom p _)
    (liveCase_putLeafFull p _ hRL' hsa hp)
    (opCaseOK_putNewSeg_of_parts p _ _ (liveCase_putNewSeg1Room p _ (by omega))
      (liveCase_putNewSegsRoom p _ (by omega)) (liveCase_putNewSegFull p _ hRL' (by omega) hsa hp)) l4'
  have hTp := opCaseOK_put_of_cases p _ _ hm (treeCase_putLeafRoom p _)
    (treeCase_putLeafFull p _ hRL' hsa)
    (opCaseOK_putNewSeg_of_parts p _ _ (treeCase_putNewSeg1Room p _ (by omega))
      (treeCase_putNewSegsRoom p _ (by omega)) (treeCase_putNewSegFull p _ hRL' (by omega) hsa))
  have hPp := opCaseOK_put_of_cases p _ _ hm (putInvCase_putLeafRoom p _ hRL')
    (putInvCase_putLeafFull p _ hRL' hsa)
    (opCaseOK_putNewSeg_of_parts p _ _ (putInvCase_putNewSeg1Room p _ hRL' (by omega))
      (putInvCase_putNewSegsRoom p _ hRL' (by omega)) (putInvCase_putNewSegFull p _ hRL' (by omega) hsa))
  have hOp := opCaseOK_put_of_cases p _ _ hm (rangeCase_putLeafRoom p _)
    (rangeCase_putLeafFull p _ hRL' hsa)
    (opCaseOK_putNewSeg_of_parts p _ _ (rangeCase_putNewSeg1Room p _ (by omega))
      (rangeCase_putNewSegsRoom p _ (by omega)) (rangeCase_putNewSegFull p _ hRL' (by omega) hsa))
  have hTIRH := opCaseOKH_treeInvRange_delMergeRL p _
    (delStepsQdLH_of_openR p _ (by omega) hsa hRL' hRP' hRK' hRH' hU hHL) hMS hCo hsa hcap hRP' hRK'
  -- the delete side of the heights' walk and the fuel, at the induction's runs
  have hht : OpHtDelOKUnder p (RunTreeQ p (LatestQD p)) :=
    opHtDelOKUnder_of_joint p _ hm (by omega) hRL' hRT' hRI' hRP' hRK' hRH' htb hTp hPp hOp
      hTIRH.1 hTIRH.2.1 hTIRH.2.2 hLv hchkL
  have hfitQ : TxSegFitsOK p (RunTreeQ p (LatestQD p)) :=
    txSegFitsOK_of_takeBelowDelRHU p (by omega) _ hRL' hRK' hRH' hht htb
  -- from here as in `invGetScanOK_merges`
  have hTIR := opCaseOK_treeInvRange_delMergeRL p _
    (delStepsQdL_of_openR p _ (by omega) hsa hRL' hRP' hRK' hRH' hht htb hU hHL) hMS hCo hsa hcap
    hRP' hRK' hfitQ
  have d4' := opCaseOK_anti p _ _ hR _ _ (deadCase_delMergeL_of_rest p (RunOK p) hRL
    (opCaseOK_of_open p (RunOK p) (QDead p) (keptByReads_dead p) DelMergeDRestCase d4))
  have hTL := opCaseOK_of_cases_mergesL p _ _ hm (treeCase_putLeafRoom p _)
    (treeCase_putLeafFull p _ hRL' hsa)
    (opCaseOK_putNewSeg_of_parts p _ _ (treeCase_putNewSeg1Room p _ (by omega))
      (treeCase_putNewSegsRoom p _ (by omega)) (treeCase_putNewSegFull p _ hRL' (by omega) hsa))
    hTIR.1
  have hPIL := opCaseOK_of_cases_mergesL p _ _ hm (putInvCase_putLeafRoom p _ hRL')
    (putInvCase_putLeafFull p _ hRL' hsa)
    (opCaseOK_putNewSeg_of_parts p _ _ (putInvCase_putNewSeg1Room p _ hRL' (by omega))
      (putInvCase_putNewSegsRoom p _ hRL' (by omega)) (putInvCase_putNewSegFull p _ hRL' (by omega) hsa))
    hTIR.2.1
  have hOL := opCaseOK_of_cases_mergesL p _ _ hm (rangeCase_putLeafRoom p _)
    (rangeCase_putLeafFull p _ hRL' hsa)
    (opCaseOK_putNewSeg_of_parts p _ _ (rangeCase_putNewSeg1Room p _ (by omega))
      (rangeCase_putNewSegsRoom p _ (by omega)) (rangeCase_putNewSegFull p _ hRL' (by omega) hsa))
    hTIR.2.2
  have hDdL := opCaseOK_of_cases_mergesL p _ _ hm (deadCase_putLeafRoom p _)
    (deadCase_putLeafFull p _ hRL' hsa hth)
    (opCaseOK_putNewSeg_of_parts p _ _ (deadCase_putNewSeg1Room p _ (by omega))
      (deadCase_putNewSegsRoom p _ (by omega)) (deadCase_putNewSegFull p _ hRL' (by omega) hsa hth)) d4'
  have hLvL := opCaseOK_L_of_any p _ _ hLv
  have hT := opCaseOK_any_of_L p _ hRL' hRT' hRI' hTL hPIL hOL hLvL _ hTL
  have hPI := opCaseOK_any_of_L p _ hRL' hRT' hRI' hTL hPIL hOL hLvL _ hPIL
  have hO := opCaseOK_any_of_L p _ hRL' hRT' hRI' hTL hPIL hOL hLvL _ hOL
  have hLC := liveStateOK_of_L p _ hRL' hRT' hRI' hTL hPIL hOL hLvL
  have hDd := opCaseOK_any_of_L p _ hRL' hRT' hRI' hTL hPIL hOL hLvL _ hDdL
  have hJ := runTreeQ_of_mergesS p (by omega) hsa hcap hm (LatestQD p) (latestQD_init p (by omega))
    (latestQD_snocR p hp hht hT hPI hO hLv hDd)
    (fun _ _ h => h.1.2.1) (fun _ _ h => h.1.2.2.1)
    (opTreeOKUnder_of_cases p _ hRL' hRT' hRI' hT hPI hO)
    (putInvStateOK_of_cases p _ hRL' hRT' hRI' hT hPI hO)
    (rangeStateOK_of_cases p _ hRL' hRT' hRI' hT hPI hO)
    hfitQ
    (fun ts tx hw hr => hMF ts tx hw (hR _ _ hr))
    (delStepsJ2OK_of_openR p _ (TakeS4 p) (by omega) hsa hRL' hRP' hRK'
      (fun _ _ _ h => h.1.1.1.1) (fun _ _ _ h => h.1.1.1.2) (fun _ _ _ h => h.1.1.2)
      (fun _ _ _ h => h.1.2) (fun _ _ _ h => h.2.1) (fun _ _ _ h => h.2.2) hRH' hht htb hU hHL hLC)
    hMS hCo (replaceRootFullJ2OK_run p hsa)
  -- the joint induction at every run within reach
  intro ts tx hw z top hz htop pre key post hsplit r w hpre r' v he
  have hr := hJ ts (within_snoc_prefix p ts tx hw)
  obtain ⟨hI, hRo, hL, hH⟩ := jointHt_reached p _ hm (by omega) hRL' hRT' hRI' hRP' hRK' hRH' htb
    hTp hPp hOp hTIRH.1 hTIRH.2.1 hTIRH.2.2 hLv hchkL ts tx hw hr z top hz htop pre
    (Op.del key :: post) hsplit r w hpre
  exact hchkL ts tx hw hr z top hz htop pre key post hsplit r w hpre hI hRo hL hH r' v he

/-- The top theorem with `hchk` narrowed to the deletes whose start has the
fill, `PutInv`, the ranges and the heights (`OpDelChk2OKL`). -/
theorem invGetScanOK_merges_chkL (p : Params) (hp : MergeParamsOK p)
    (hth : 2 ≤ p.theta ∨ p.theta = 0)
    (hchkL : OpDelChk2OKL p)
    (htb : TakeBelowFuelDelOK p)
    (d4 : OpCaseOK p (RunOK p) (QDead p) DelMergeDOpenCase)
    (l4 : OpCaseOK p (RunOK p) (QLive p) DelMergeOpenCase)
    (hU : ∀ ts, UpUnlinkTreeOK (ctxOf p ts) (viewOf (treeRun p ts)))
    (hHL : ∀ ts, UpHolderLiveRunOK (ctxOf p ts) (viewOf (treeRun p ts)))
    (hMSF : ∀ ts, MergeFitsOK (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1))
    (hCoF : ∀ ts, CollapseFitsOK (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1))
    (hCoU : ∀ ts, CollapseUnlinkAllOK (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1))
    (hMF : StateOK p (RunOK p) (fun _ tx w => ∀ x o, w.madeFor.lookup x = some o → o < tx.base)) :
    InvPreserved p ∧ GetOK p ∧ ScanOK p ∧ LatestGetOK p ∧ LatestScanOK p :=
  invGetScanOK_merges p hp hth
    (opDelChk2OK_of_chk2L p hp hth hchkL htb d4 l4 hU hHL hMSF hCoF hCoU hMF)
    htb d4 l4 hU hHL hMSF hCoF hCoU hMF

end SIS.Tree
