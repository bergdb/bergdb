/-
The run machinery for the runs of `N.Within` (bergdb 025-03; NoOutsideBase.lean):
the heights, the fuel between operations and the delete with the merges,
each lemma as in its own file (named in its docstring) with `Within` the runs with no
key node outside the level bounds.
-/
import SIS.Tree.NoOutsideRun2

set_option autoImplicit false

namespace SIS.Tree.N

open SIS SIS.Check

/-- As `SIS.Tree.ht_reachedU`, for the runs of `N.Within`. -/
theorem ht_reachedU (p : Params) (hM : 2 ≤ p.M) (R : Struct BVal → Time → Prop)
    (hdel : OpHtDelOKUnder p R) (ts : List Tx) (tx : Tx)
    (hw : Within p (ts ++ [tx])) (hr : R (treeRun p ts) ts.length) (hR : RunLinksOK p (treeRun p ts) ts.length)
    (hvo : ViewHtOK (htOracleOf p (treeRun p ts)) tx.base (ctxOf p ts))
    (z : NodeId) (top : Top)
    (hz : lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z)
    (htop : topOf p (ctxOf p ts).view z = .ok top) :
    ∀ pre post, tx.ops = pre ++ post → ∀ r w,
      (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
      HtInv (htOracleOf p (treeRun p ts)) tx.base (ctxOf p ts) w := by
  intro pre
  suffices hk : ∀ k, ∀ pre : List Op, pre.length = k → ∀ post, tx.ops = pre ++ post → ∀ r w,
      (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
      HtInv (htOracleOf p (treeRun p ts)) tx.base (ctxOf p ts) w from hk pre.length pre rfl
  intro k
  induction k with
  | zero =>
    intro pre hl _ _ r w h
    have hnil : pre = [] := List.eq_nil_of_length_eq_zero hl
    subst hnil
    simp only [List.mapM_nil, pure, ReaderT.pure, StateT.pure, Except.pure, Except.ok.injEq,
      Prod.mk.injEq] at h
    rw [← h.2]
    exact htInv_start _ _ _ top
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
          have hI1 := ih pre' hl' (op :: post) hsplit' r1 w1 h1
          have hbk := putBook_reached p ts tx hw hR z top htop pre' r1 w1 h1
          have hB := putBase_of_run p ts tx hw hR
          rw [← h.2]
          cases op with
          | put key hv0 =>
            exact (ht_putKv_put tx.base (appendFrameOK tx.base) key hv0 (ctxOf p ts) w1 hvo
              (by simp [ctxOf]) hbk.book hI1 hM hB.wf hbk.klongs a w2 h2).2.1
          | del key =>
            exact hdel ts tx hw hr z top hz htop pre' key post hsplit' r1 w1 h1 hvo hB.wf hbk.book
              hbk.klongs hI1 a w2 h2

/-- As `SIS.Tree.execW_htCacheU`, for the runs of `N.Within`. -/
theorem execW_htCacheU (p : Params) (hM : 2 ≤ p.M) (R : Struct BVal → Time → Prop)
    (hdel : OpHtDelOKUnder p R) (ts : List Tx) (tx : Tx)
    (hw : Within p (ts ++ [tx])) (hr : R (treeRun p ts) ts.length) (hR : RunLinksOK p (treeRun p ts) ts.length)
    (hK : KindsAllOK p (treeRun p ts)) (hA : HeightAllOK p (treeRun p ts) ts.length)
    (bs : List Bool) (w : W)
    (he : execW p tx (ts.length + 1) (view (treeSpec p) (treeRun p ts) ts.length) = .ok (bs, w)) :
    HtCache (ctxOf p ts) (htOracleOf p (treeRun p ts)) w := by
  have hvo := viewHtOK_of_run p ts tx hw hR hK hA
  unfold execW runOps runOpsFrom at he
  cases hz : lastTop (view (treeSpec p) (treeRun p ts) ts.length) with
  | none => simp [hz] at he
  | some z =>
    simp only [hz] at he
    cases ht : topOf p (rootless (view (treeSpec p) (treeRun p ts) ts.length)) z with
    | error e => simp [ht] at he
    | ok top =>
      simp only [ht] at he
      have hrun := boundsOK_ok p _ bs w he
      exact (ht_reachedU p hM R hdel ts tx hw hr hR hvo z top hz ht tx.ops [] (by simp) bs w
        hrun).cache

set_option maxHeartbeats 1600000 in
/-- `SIS.Tree.htStart_reachedU` for the runs of `N.Within`, without `htb`: every
height the writer knows is at most H (`heights_le_H_of_noOutside`), so below the
fuel. -/
theorem htStart_reachedU (p : Params) (hM : 2 ≤ p.M) (R : Struct BVal → Time → Prop)
    (hRL : ∀ P t, R P t → RunLinksOK p P t) (hRK : ∀ P t, R P t → KindsAllOK p P)
    (hRH : ∀ P t, R P t → HeightAllOK p P t) (hht : OpHtDelOKUnder p R)
    (ts : List Tx) (tx : Tx) (hw : Within p (ts ++ [tx]))
    (hr : R (treeRun p ts) ts.length) (z : NodeId) (top : Top)
    (hz : lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z)
    (htop : topOf p (ctxOf p ts).view z = .ok top) (pre post : List Op)
    (hsplit : tx.ops = pre ++ post) (r : List Bool) (w : W)
    (hpre : (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w)) :
    ViewHtOK (htOracleOf p (treeRun p ts)) tx.base (ctxOf p ts) ∧
      ViewKlongsWf p (ctxOf p ts).view ∧
      BaseHeights (ctxOf p ts) (htOracleOf p (treeRun p ts)) (viewOf (treeRun p ts)) ∧
      (∀ y h, htOracleOf p (treeRun p ts) y h → h ≤ p.H) ∧
      Book tx.base (ctxOf p ts) w ∧ HtInv (htOracleOf p (treeRun p ts)) tx.base (ctxOf p ts) w ∧
      WriterKlongsWf w ∧ UntakenBound (p.fuel - 1) w := by
  have hR := hRL _ _ hr
  have hK := hRK _ _ hr
  have hA := hRH _ _ hr
  have hvo := viewHtOK_of_run p ts tx hw hR hK hA
  have hi := ht_reachedU p hM R hht ts tx hw hr hR hvo z top hz htop pre post
    hsplit r w hpre
  have hbk := putBook_reached p ts tx hw hR z top htop pre r w hpre
  have hB := putBase_of_run p ts tx hw hR
  have hle := heights_le_H_of_noOutside p ts tx hw.w hw.no z top hz htop pre post hsplit r w hpre
  have htimes : StructTimesLE (treeRun p ts) ts.length := treeRun_timesLE p ts
  have hbase := baseHeights_of p (treeRun p ts) ts.length (ctxOf p ts) rfl
    (by simp [ctxOf]) htimes hR.1 hK hA
  refine ⟨hvo, hB.wf, hbase, ?_, hbk.book, hi, hbk.klongs, fun x g h hm _ => ?_⟩
  · rintro y h ⟨ny, _, _, _, hny⟩
    exact hny ▸ heightOf_le p ny.level
  · have := hle x g h hm
    have := fuel_gt_H p
    omega

set_option maxHeartbeats 1600000 in
/-- As `SIS.Tree.txSegFitsOK_of_takeBelowDelRHU`, for the runs of `N.Within`. -/
theorem txSegFitsOK_of_takeBelowDelRHU (p : Params) (hM : 2 ≤ p.M) (R : Struct BVal → Time → Prop)
    (hRL : ∀ P t, R P t → RunLinksOK p P t) (hRK : ∀ P t, R P t → KindsAllOK p P)
    (hRH : ∀ P t, R P t → HeightAllOK p P t) (hht : OpHtDelOKUnder p R) : TxSegFitsOK p R := by
  intro ts tx hw hr z top hz htop pre post hsplit r w hpre
  obtain ⟨hvo, -, hbase, hHb, hbk, hi, -, hub⟩ := htStart_reachedU p hM R hRL hRK hRH hht
    ts tx hw hr z top hz htop pre post hsplit r w hpre
  refine segFits_of_heightsU hbk hi.cache hvo.heights _ hbase (p.fuel - 1) _ ?_
  intro x n hn h hh
  rcases hh with ⟨g, hm⟩ | hh
  · exact hub x g h hm (wNode_cases _ _ _ _ _ hn).1
  · have := hHb x h hh
    have := fuel_gt_H p
    omega

/-- As `SIS.Tree.txSegFitsOK_of_takeBelowDelR2U`, for the runs of `N.Within`. -/
theorem txSegFitsOK_of_takeBelowDelR2U (p : Params) (hM : 2 ≤ p.M)
    (R : Struct BVal → Time → Prop) (hRP : ∀ P t, R P t → PointersOK P)
    (hRL : ∀ P t, R P t → RunLinksOK p P t) (hRK : ∀ P t, R P t → KindsAllOK p P)
    (hRH : ∀ P t, R P t → HeightAllOK p P t) (hchk : OpDelChk2OK p) : TxSegFitsOK p R :=
  txSegFitsOK_of_takeBelowDelRHU p hM R hRL hRK hRH (opHtDelOKUnder_of_chk2 p hM R hRP hRK hchk)


/-- As `SIS.Tree.delStepsCaseOK_fullH`, for the runs of `N.Within`. -/
theorem delStepsCaseOK_fullH (p : Params) (R : Struct BVal → Time → Prop) (hM : 2 ≤ p.M)
    (hsa2 : 2 ≤ p.splitAbove)
    (hRL : ∀ P t, R P t → RunLinksOK p P t)
    (hP : ∀ ts, Within p ts → PointersOK (treeRun p ts))
    (hRK : ∀ P t, R P t → KindsAllOK p P) (hRH : ∀ P t, R P t → HeightAllOK p P t)
    (hht : OpHtDelOKUnder p R)
    (hRoot : ∀ ts, DelFullRootStepOK (ctxOf p ts) (viewOf (treeRun p ts))) :
    DelStepsCaseOK p R DelFullM := by
  intro ts tx hw hr z top hz htop ops op post hops r w hpre hI hRO hF key hop hPc hA _ _
  obtain ⟨pre, cv, L0, n0, hop', _, hK, hne0, hkeep0, hfull0⟩ := hPc
  subst hop'
  cases hop
  have hkey : keyWf (pre ++ [cv]) = true := within_op_keyWf p ts tx hw ops _ post hops
  obtain ⟨rk, hrk, _⟩ := keyLeaf_rk hK
  have hB := putBase_of_run p ts tx hw (hRL _ _ hr)
  have hbook := putBook_reached p ts tx hw (hRL _ _ hr) z top htop ops r w hpre
  obtain ⟨hv, hk, hb0, hi0⟩ := kd_context p hM hP ts tx hw top ops (.del (pre ++ [cv]) :: post) hops r w hpre
  have hwts : Within p ts := by
    have := within_take p (ts ++ [tx]) hw ts.length
    simpa using this
  have hKall := treeRun_kindsAllOK p hM hP ts hwts
  have hICEk : ICEFromKinds (ctxOf p ts) (viewOf (treeRun p ts)) (kindOracleOf p (treeRun p ts)) tx.base :=
    fun v hb hi hun => innerChildren_of_kinds p (treeRun p ts) tx.base (ctxOf p ts) v rfl hKall
      (hP ts hwts) hb hi.cache hun
  have hJ0 : KdJ (ctxOf p ts) tx.base top (kindOracleOf p (treeRun p ts)) tx.base w := ⟨hbook, hb0, hi0⟩
  obtain ⟨hvo, hkw, _, _, _, hhi, hwfw, hub⟩ := htStart_reachedU p hM R hRL hRK hRH hht ts tx hw hr z top
    hz htop ops (.del (pre ++ [cv]) :: post) hops r w hpre
  refine writerWP_del_toLeafMKH (ctxOf p ts) _ (viewCoherent_ctxOf p ts) pre cv rk w
    (KdHtJ (ctxOf p ts) tx.base top (kindOracleOf p (treeRun p ts)) tx.base (htOracleOf p (treeRun p ts)))
    (fun s f x v hJ hx => kdhtJ_descendLte _ top hB _ tx.base hv hk hvo hkw s f x v hJ hx)
    (fun s fd L n v hJ hL hlk hleaf hfd => kdhtJ_pathAdd _ top hB _ tx.base hv hvo s fd L n v hJ hL hlk hleaf hfd)
    (kdhtJ_start _ top hB _ tx.base hv hvo w hJ0 hhi hwfw hub) hrk (hI.pathUntaken _) hI.wf _ ?_ ?_
  · intro v hv'
    unfold fresh
    wpSimplify
    exact hv'
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
    refine writerWP_mono (hA g h v hv') ?_
    intro _ v' hv'' hFv' key' hk'
    have := runGet_of_delInvF p ts w v' (pre ++ [cv]) hv''.1 hI hF hFv' key' hk'
    simpa [Op.key, Op.value] using this

set_option maxHeartbeats 1600000 in
/-- As `SIS.Tree.delStepsCaseJ2OK_fullRH`, for the runs of `N.Within`. -/
theorem delStepsCaseJ2OK_fullRH (p : Params) (R : Struct BVal → Time → Prop)
    (S : List Tx → Tx → W → Prop) (hM : 2 ≤ p.M) (hsa2 : 2 ≤ p.splitAbove)
    (hRL : ∀ P t, R P t → RunLinksOK p P t)
    (hRP : ∀ P t, R P t → PointersOK P) (hRK : ∀ P t, R P t → KindsAllOK p P)
    (hSI : ∀ ts tx w, S ts tx w → PutInv (ctxOf p ts) (viewOf (treeRun p ts)) w)
    (hSV : ∀ ts tx w, S ts tx w → LeafVals (ctxOf p ts) (viewOf (treeRun p ts)) tx.base w)
    (hSB : ∀ ts tx w, S ts tx w → tx.base ≤ w.next)
    (hSR : ∀ ts tx w, S ts tx w →
      RangeOrder (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey)
    (hSF : ∀ ts tx w, S ts tx w →
      SegFits (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) (p.fuel - 1) w.top.rootKey)
    (hRH : ∀ P t, R P t → HeightAllOK p P t) (hht : OpHtDelOKUnder p R) :
    DelStepsCaseJ2OK p R S DelFullM := by
  intro ts tx hw hr z top hz htop ops op post hops r w hpre hS hJ key hop hPc hA _ _
  obtain ⟨pre, cv, L0, n0, hop', _, hK, hne0, hkeep0, hfull0⟩ := hPc
  subst hop'
  cases hop
  have hI := hSI ts tx w hS
  have hRO := hSR ts tx w hS
  have hF := hSF ts tx w hS
  have hkey : keyWf (pre ++ [cv]) = true := within_op_keyWf p ts tx hw ops _ post hops
  obtain ⟨rk, hrk, _⟩ := keyLeaf_rk hK
  have hB := putBase_of_run p ts tx hw (hRL _ _ hr)
  have hbook := putBook_reached p ts tx hw (hRL _ _ hr) z top htop ops r w hpre
  have hG := putInvG_of_book _ _ tx.base top w hB hbook
  have hLV := leafVals_all (hSV ts tx w hS) hkey hrk
  have hpos : 0 < (ctxOf p ts).i := by simp [ctxOf]
  obtain ⟨hv, hk, hb0, hi0⟩ := kd_contextR p hM ts tx (hRP _ _ hr) (hRK _ _ hr) hw top ops (.del (pre ++ [cv]) :: post) hops r w hpre
  have hwts : Within p ts := by
    have := within_take p (ts ++ [tx]) hw ts.length
    simpa using this
  have hKall := hRK _ _ hr
  have hICEk : ICEFromKinds (ctxOf p ts) (viewOf (treeRun p ts)) (kindOracleOf p (treeRun p ts)) tx.base :=
    fun v hb hi hun => innerChildren_of_kinds p (treeRun p ts) tx.base (ctxOf p ts) v rfl hKall
      (hRP _ _ hr) hb hi.cache hun
  have hJ0 : KdJ (ctxOf p ts) tx.base top (kindOracleOf p (treeRun p ts)) tx.base w := ⟨hbook, hb0, hi0⟩
  obtain ⟨hvo, hkw, _, _, _, hhi, hwfw, hub⟩ := htStart_reachedU p hM R hRL hRK hRH hht ts tx hw hr z top
    hz htop ops (.del (pre ++ [cv]) :: post) hops r w hpre
  refine writerWP_del_toLeafMKH (ctxOf p ts) _ (viewCoherent_ctxOf p ts) pre cv rk w
    (KdHtJ (ctxOf p ts) tx.base top (kindOracleOf p (treeRun p ts)) tx.base (htOracleOf p (treeRun p ts)))
    (fun s f x v hJ hx => kdhtJ_descendLte _ top hB _ tx.base hv hk hvo hkw s f x v hJ hx)
    (fun s fd L n v hJ hL hlk hleaf hfd => kdhtJ_pathAdd _ top hB _ tx.base hv hvo s fd L n v hJ hL hlk hleaf hfd)
    (kdhtJ_start _ top hB _ tx.base hv hvo w hJ0 hhi hwfw hub) hrk (hI.pathUntaken _) hI.wf _ ?_ ?_
  · intro v hv'
    unfold fresh
    wpSimplify
    exact hv'
  · intro L n P w3 hL hn hnl hr03 hJ3 hlk3 hp3' hlinkP hXD hlkX
    obtain ⟨hne, hkeep, hfull⟩ := keyLeaf_all2 hK hrk
      (fun _ m => bitsUnion m.lastBitmap (m.bitsOf cv) ≠ m.lastBitmap ∧
        m.allKeysIn (bitsUnion m.lastBitmap (m.bitsOf cv)) = false ∧ ¬ DelRoom (ctxOf p ts) cv m)
      ⟨hne0, hkeep0, hfull0⟩ L n hL hn hnl
    have hPOK := pathOK_of_toLeaf (ctxOf p ts) _ w w3 P n hI hr03 hp3' hlinkP hlkX
    have hJ3' : TakeJ2 (ctxOf p ts) (viewOf (treeRun p ts)) tx.base w3 := takeJ2_of_readsAs _ _ _ w w3 hJ hr03
    have hJ2 := writerWP_appendDeleteKlong_full_j2_any (ctxOf p ts) _ tx.base hpos
      (delFullRootJ2OK_ctx p hsa2 ts tx.base) w3
      (putInv_of_readsAs _ _ w w3 hI hr03) (putInvG_of_readsAs _ _ w w3 hG hr03)
      (by rw [hr03.1, hr03.2.1]; exact hRO) hJ3' (by rw [hr03.2.2.2.2]; exact hSB ts tx w hS) hsa2
      P.length _ _ _ hPOK cv n (by show (wNode _ _ w (nodeAt w.top.rootKey P P.length)).getD _ = n; rw [hXD, hn]; rfl)
      hnl hne hfull (fun y hy => by rw [hr03.1]; exact (hLV L n hL hn hnl y hy).1)
    simp only [hXD] at hJ2
    refine writerWP_deleteUpward_full (ctxOf p ts) L n P.length cv (pre ++ [cv]) w3 hlk3 hne hkeep
      (fun v => DelInvJ (ctxOf p ts) (viewOf (treeRun p ts)) w (pre ++ [cv]) (p.fuel + 1)
        (kindOracleOf p (treeRun p ts)) tx.base tx.base v) _
      (writerWP_mono (writerWP_and (writerWP_appendDeleteKlong_full_delH (ctxOf p ts) _ (viewCoherent_ctxOf p ts)
        _ tx.base (delFullRootStepOK_ctx p ts) _ (delFullFitsOKR_run p ts tx hw (hRL _ _ hr) (hRK _ _ hr) (hRH _ _ hr))
        hsa2 hv hk hICEk w pre cv rk tx.base top hB hI hRO hF
        hkey hrk L n P w3 hL hn hnl hne hfull hr03 hJ3.1 hJ3.2 hp3' hlinkP hXD hlkX) hJ2)
        (fun _ v hv' => ⟨hv'.1, hv'.2.1, hv'.2.2⟩)) ?_
    intro g h v hv'
    exact writerWP_mono (hA g h v hv') (fun _ v' hv'' => hv''.2.1)

/-- As `SIS.Tree.opCaseOK_L_of_any`, for the runs of `N.Within`. -/
theorem opCaseOK_L_of_any (p : Params) (R : Struct BVal → Time → Prop)
    (Q : List Tx → Op → W → W → Prop) (h : OpCaseOK p R Q AnyOp) : OpCaseOK p R Q AnyOpL :=
  fun ts tx hw hr z top hz htop pre op post hs r w hpre hI hRO _ =>
    h ts tx hw hr z top hz htop pre op post hs r w hpre hI hRO trivial

/-- As `SIS.Tree.jointLive_reached`, for the runs of `N.Within`. -/
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

/-- As `SIS.Tree.opCaseOK_any_of_L`, for the runs of `N.Within`. -/
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

/-- As `SIS.Tree.liveStateOK_of_L`, for the runs of `N.Within`. -/
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

/-- As `SIS.Tree.opCaseOK_of_cases_mergesL`, for the runs of `N.Within`. -/
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

/-- As `SIS.Tree.opCaseOK_of_any`, for the runs of `N.Within`. -/
theorem opCaseOK_of_any (p : Params) (R : Struct BVal → Time → Prop)
    (Q : List Tx → Op → W → W → Prop) (C : Ctx → View BVal → W → Op → Prop)
    (h : OpCaseOK p R Q AnyOp) : OpCaseOK p R Q C :=
  fun ts tx hw hr z top hz htop pre op post hs r w hpre hI hRO _ =>
    h ts tx hw hr z top hz htop pre op post hs r w hpre hI hRO trivial

/-- As `SIS.Tree.delStepsCaseQd_fullH`, for the runs of `N.Within`. -/
theorem delStepsCaseQd_fullH (p : Params) (R : Struct BVal → Time → Prop) (hM : 2 ≤ p.M)
    (hsa2 : 2 ≤ p.splitAbove)
    (hRL : ∀ P t, R P t → RunLinksOK p P t)
    (hRP : ∀ P t, R P t → PointersOK P)
    (hRK : ∀ P t, R P t → KindsAllOK p P) (hRH : ∀ P t, R P t → HeightAllOK p P t)
    (hht : OpHtDelOKUnder p R)
    (hRoot : ∀ ts, DelFullRootStepOK (ctxOf p ts) (viewOf (treeRun p ts))) :
    DelStepsCaseQd p R DelFullM := by
  intro ts tx hw hr z top hz htop ops op post hops r w hpre hI hRO hF key hop hPc hA _ _
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
  obtain ⟨hvo, hkw, _, _, _, hhi, hwfw, hub⟩ := htStart_reachedU p hM R hRL hRK hRH hht ts tx hw hr z top
    hz htop ops (.del (pre ++ [cv]) :: post) hops r w hpre
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

/-- As `SIS.Tree.opCaseOK_qdW_delMergeRL`, for the runs of `N.Within`. -/
theorem opCaseOK_qdW_delMergeRL (p : Params) (R : Struct BVal → Time → Prop) (hS : DelStepsQdL p R)
    (hM : ∀ ts, MergeStepOK (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1))
    (hC : ∀ ts, CollapseStepOK (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1))
    (hsa2 : 2 ≤ p.splitAbove) (hcap : 1 ≤ p.mergeMax)
    (hRP : ∀ P t, R P t → PointersOK P) (hRK : ∀ P t, R P t → KindsAllOK p P) (hfit : TxSegFitsOK p R) :
    OpCaseOK p R (fun ts _ _ w' => QdW p ts w') DelMergeCaseL := by
  have hf2 : 2 ≤ p.fuel + 1 := by unfold Params.fuel; omega
  intro ts tx hw hr z top hz htop pre op post hops r w hpre hI hRO hP
  obtain ⟨⟨key, hop, hmerges⟩, hLCw⟩ := hP
  have hF0 := hfit ts tx hw hr z top hz htop pre (op :: post) hops r w hpre
  have hwts : Within p ts := by
    have := within_take p (ts ++ [tx]) hw ts.length
    simpa using this
  have hfresh : ∀ q ∈ treeRun p ts, q.1 < tx.base := by
    have := (hw.w.2 ts.length (by simp)).1
    simpa using this
  have hK := hRK _ _ hr
  have hv : ViewIdsBelow tx.base (ctxOf p ts).view :=
    viewIdsBelow_rootless _ _ (viewIdsBelow_view p (treeRun p ts) ts.length tx.base hfresh)
  have hk : ViewKinds (kindOracleOf p (treeRun p ts)) tx.base (ctxOf p ts) :=
    viewKinds_of p (treeRun p ts) ts.length tx.base hfresh (treeRun_timesLE p ts) (hRP _ _ hr) hK
  have hICEk : ICEFromKinds (ctxOf p ts) (viewOf (treeRun p ts)) (kindOracleOf p (treeRun p ts)) tx.base :=
    fun v hb hi hun => innerChildren_of_kinds p (treeRun p ts) tx.base (ctxOf p ts) v rfl hK
      (hRP _ _ hr) hb hi.cache hun
  exact hS ts tx hw hr z top hz htop pre op post hops r w hpre hI hRO hF0 key hop ⟨⟨key, hop, hmerges⟩, hLCw⟩
    (fun g h v hv' => writerWP_afterDelete_del key g h (ctxOf p ts) _ (viewCoherent_ctxOf p ts)
      (p.fuel + 1) hf2 (hM ts) (hC ts) _ _ hv hk hICEk hsa2 hcap w key v hv')
    (fun g h merged v hv' => writerWP_mergeUp_del key g (ctxOf p ts) _ (viewCoherent_ctxOf p ts)
      (p.fuel + 1) hf2 (hM ts) _ _ hv hk hICEk hsa2 hcap w key p.fuel h merged v hv')
    (fun seg v hv' => writerWP_collapseRoot_del key seg (ctxOf p ts) _ (viewCoherent_ctxOf p ts)
      (p.fuel + 1) hf2 (hC ts) w key _ _ hv hk hICEk hsa2 v hv')

/-- As `SIS.Tree.opCaseOK_treeInvRange_delMergeRL`, for the runs of `N.Within`. -/
theorem opCaseOK_treeInvRange_delMergeRL (p : Params) (R : Struct BVal → Time → Prop) (hS : DelStepsQdL p R)
    (hM : ∀ ts, MergeStepOK (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1))
    (hC : ∀ ts, CollapseStepOK (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1))
    (hsa2 : 2 ≤ p.splitAbove) (hcap : 1 ≤ p.mergeMax)
    (hRP : ∀ P t, R P t → PointersOK P) (hRK : ∀ P t, R P t → KindsAllOK p P) (hfit : TxSegFitsOK p R) :
    OpCaseOK p R (QTree p) DelMergeCaseL ∧ OpCaseOK p R (QPutInv p) DelMergeCaseL ∧
      OpCaseOK p R (QRange p) DelMergeCaseL := by
  have h := opCaseOK_qdW_delMergeRL p R hS hM hC hsa2 hcap hRP hRK hfit
  refine ⟨?_, ?_, ?_⟩
  · intro ts tx hw hr z top hz htop pre op post hops r w hpre hI hRO hP
    exact writerWP_mono (h ts tx hw hr z top hz htop pre op post hops r w hpre hI hRO hP)
      (fun _ w' hq => hq.1.tree)
  · intro ts tx hw hr z top hz htop pre op post hops r w hpre hI hRO hP
    exact writerWP_mono (h ts tx hw hr z top hz htop pre op post hops r w hpre hI hRO hP)
      (fun _ w' hq _ => hq.1)
  · intro ts tx hw hr z top hz htop pre op post hops r w hpre hI hRO hP
    exact writerWP_mono (h ts tx hw hr z top hz htop pre op post hops r w hpre hI hRO hP)
      (fun _ w' hq _ => hq.2)

/-- As `SIS.Tree.opCaseOK_or`, for the runs of `N.Within`. -/
theorem opCaseOK_or (p : Params) (R : Struct BVal → Time → Prop) (Q : List Tx → Op → W → W → Prop)
    (C C1 C2 : Ctx → View BVal → W → Op → Prop)
    (hcov : ∀ c base w op, C c base w op → C1 c base w op ∨ C2 c base w op)
    (h1 : OpCaseOK p R Q C1) (h2 : OpCaseOK p R Q C2) : OpCaseOK p R Q C :=
  fun ts tx hw hr z top hz htop pre op post hs r w hpre hI hRO hC =>
    (hcov _ _ _ _ hC).elim
      (fun h => h1 ts tx hw hr z top hz htop pre op post hs r w hpre hI hRO h)
      (fun h => h2 ts tx hw hr z top hz htop pre op post hs r w hpre hI hRO h)

/-- As `SIS.Tree.liveCase_delMerge_of_rest`, for the runs of `N.Within`. -/
theorem liveCase_delMerge_of_rest (p : Params) (R : Struct BVal → Time → Prop)
    (hRL : ∀ P t, R P t → RunLinksOK p P t)
    (hrest : OpCaseOK p R (QLive p) DelMergeRestCase) :
    OpCaseOK p R (QLive p) DelMergeCase :=
  opCaseOK_or p R (QLive p) DelMergeCase DelRoomFillCase _
    (fun c base w op h => (Classical.em (DelRoomFillCase c base w op)).elim Or.inl
      (fun hn => Or.inr ⟨h, hn⟩))
    (liveCase_delRoomFill p R hRL) hrest

/-- As `SIS.Tree.deadCase_delMergeL_of_rest`, for the runs of `N.Within`. -/
theorem deadCase_delMergeL_of_rest (p : Params) (R : Struct BVal → Time → Prop)
    (hRL : ∀ P t, R P t → RunLinksOK p P t)
    (hrest : OpCaseOK p R (QDead p) DelMergeDRestCase) :
    OpCaseOK p R (QDead p) (fun c base w op =>
      DelMergeCase c base w op ∧ LiveCounts c.p (wNode c.p base w) c.i w.top.rootKey) :=
  opCaseOK_or p R (QDead p) _ DelRoomFillDCase DelMergeDRestCase
    (fun c base w op h => (Classical.em (DelRoomFillDCase c base w op)).elim Or.inl
      (fun hn => Or.inr ⟨h.1, hn⟩))
    (deadCase_delRoomFill p R hRL) hrest

/-- As `SIS.Tree.delStepsCaseOK_emptyCascLHG`, for the runs of `N.Within`. -/
theorem delStepsCaseOK_emptyCascLHG (p : Params) (R : Struct BVal → Time → Prop) (hM : 2 ≤ p.M)
    (hsa2 : 2 ≤ p.splitAbove)
    (hRL : ∀ P t, R P t → RunLinksOK p P t)
    (hP : ∀ ts, Within p ts → PointersOK (treeRun p ts))
    (hRK : ∀ P t, R P t → KindsAllOK p P) (hRH : ∀ P t, R P t → HeightAllOK p P t)
    (hht : OpHtDelOKUnder p R)
    (hU : ∀ ts, UpUnlinkTreeOK (ctxOf p ts) (viewOf (treeRun p ts)))
    (hHL : ∀ ts, UpHolderLiveRunOK (ctxOf p ts) (viewOf (treeRun p ts)))
    (hLC : StateOK p R (fun ts _ w => LiveCountsW p ts w)) :
    DelStepsCaseOK p R DelEmptyCascM := by
  intro ts tx hw hr z top hz htop ops op post hops r w hpre hI hRO hF key hop hPc hA hMU hCR
  have hLCw := hLC ts tx hw hr z top hz htop ops (op :: post) hops r w hpre
  obtain ⟨pre, cv, L0, n0, hop', hm, hK, hne0, hall0, P0, hP0, hX0, hl0, _⟩ := hPc
  subst hop'
  cases hop
  obtain ⟨hvo, hkw, hbase, hHb, _, hhi, hwfw, hub⟩ := htStart_reachedU p hM R hRL hRK hRH hht ts tx hw hr z top
    hz htop ops (.del (pre ++ [cv]) :: post) hops r w hpre
  have hkey : keyWf (pre ++ [cv]) = true := within_op_keyWf p ts tx hw ops _ post hops
  obtain ⟨rk, hrk, _⟩ := keyLeaf_rk hK
  have hB := putBase_of_run p ts tx hw (hRL _ _ hr)
  have hbook := putBook_reached p ts tx hw (hRL _ _ hr) z top htop ops r w hpre
  have hICE := innerChildren_reached p hM hP ts tx hw top ops (.del (pre ++ [cv]) :: post) hops r w hpre
    (fun x hx => hI.untaken x (tReach_reachS _ _ _ _ hx))
  obtain ⟨hv, hk, hb0, hi0⟩ := kd_context p hM hP ts tx hw top ops (.del (pre ++ [cv]) :: post) hops r w hpre
  have hwts : Within p ts := by
    have := within_take p (ts ++ [tx]) hw ts.length
    simpa using this
  have hKall := treeRun_kindsAllOK p hM hP ts hwts
  have hICEk : ICEFromKinds (ctxOf p ts) (viewOf (treeRun p ts)) (kindOracleOf p (treeRun p ts)) tx.base :=
    fun v hb hi hun => innerChildren_of_kinds p (treeRun p ts) tx.base (ctxOf p ts) v rfl hKall
      (hP ts hwts) hb hi.cache hun
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
    _ (fun v hv' => by unfold fresh; wpSimplify; exact hv') ?_
  intro v hv' hFv key' hk'
  have := runGet_of_delInvF p ts w v (pre ++ [cv]) hv'.1 hI hF hFv key' hk'
  simpa [Op.key, Op.value] using this

/-- As `SIS.Tree.delStepsCaseJ2OK_emptyCascRLHG`, for the runs of `N.Within`. -/
theorem delStepsCaseJ2OK_emptyCascRLHG (p : Params) (R : Struct BVal → Time → Prop)
    (S : List Tx → Tx → W → Prop) (hM : 2 ≤ p.M) (hsa2 : 2 ≤ p.splitAbove)
    (hRL : ∀ P t, R P t → RunLinksOK p P t)
    (hRP : ∀ P t, R P t → PointersOK P) (hRK : ∀ P t, R P t → KindsAllOK p P)
    (hSI : ∀ ts tx w, S ts tx w → PutInv (ctxOf p ts) (viewOf (treeRun p ts)) w)
    (hSV : ∀ ts tx w, S ts tx w → LeafVals (ctxOf p ts) (viewOf (treeRun p ts)) tx.base w)
    (hSR : ∀ ts tx w, S ts tx w →
      RangeOrder (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey)
    (hSF : ∀ ts tx w, S ts tx w →
      SegFits (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) (p.fuel - 1) w.top.rootKey)
    (hSM : ∀ ts tx w, S ts tx w → ∀ x o, w.madeFor.lookup x = some o → o < tx.base)
    (hRH : ∀ P t, R P t → HeightAllOK p P t)
    (hht : OpHtDelOKUnder p R)
    (hU : ∀ ts, UpUnlinkTreeOK (ctxOf p ts) (viewOf (treeRun p ts)))
    (hHL : ∀ ts, UpHolderLiveRunOK (ctxOf p ts) (viewOf (treeRun p ts)))
    (hLC : StateOK p R (fun ts _ w => LiveCountsW p ts w)) :
    DelStepsCaseJ2OK p R S DelEmptyCascM := by
  intro ts tx hw hr z top hz htop ops op post hops r w hpre hS hJ key hop hPc hA hMU hCR
  have hLCw := hLC ts tx hw hr z top hz htop ops (op :: post) hops r w hpre
  obtain ⟨pre, cv, L0, n0, hop', hm, hK, hne0, hall0, P0, hP0, hX0, hl0, _⟩ := hPc
  subst hop'
  cases hop
  obtain ⟨hvo, hkw, hbase, hHb, _, hhi, hwfw, hub⟩ := htStart_reachedU p hM R hRL hRK hRH hht ts tx hw hr z top
    hz htop ops (.del (pre ++ [cv]) :: post) hops r w hpre
  have hI := hSI ts tx w hS
  have hkey : keyWf (pre ++ [cv]) = true := within_op_keyWf p ts tx hw ops _ post hops
  obtain ⟨rk, hrk, _⟩ := keyLeaf_rk hK
  have hB := putBase_of_run p ts tx hw (hRL _ _ hr)
  have hbook := putBook_reached p ts tx hw (hRL _ _ hr) z top htop ops r w hpre
  have hICE := innerChildren_reachedR p hM ts tx (hRP _ _ hr) (hRK _ _ hr) hw top ops (.del (pre ++ [cv]) :: post) hops r w hpre
    (fun x hx => hI.untaken x (tReach_reachS _ _ _ _ hx))
  have hLV := leafVals_all (hSV ts tx w hS) hkey hrk
  obtain ⟨hv, hk, hb0, hi0⟩ := kd_contextR p hM ts tx (hRP _ _ hr) (hRK _ _ hr) hw top ops (.del (pre ++ [cv]) :: post) hops r w hpre
  have hICEk : ICEFromKinds (ctxOf p ts) (viewOf (treeRun p ts)) (kindOracleOf p (treeRun p ts)) tx.base :=
    fun v hb hi hun => innerChildren_of_kinds p (treeRun p ts) tx.base (ctxOf p ts) v rfl (hRK _ _ hr)
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
  exact writerWP_del_emptyAnyMJKLHG (ctxOf p ts) _ (viewCoherent_ctxOf p ts) pre cv rk w tx.base top hB hbook
    _ tx.base hv hk hb0 hi0
    hI (hSR ts tx w hS) (hSF ts tx w hS) hICE hkey hrk (keyLeaf_all2 hK hrk _ ⟨hne0, hall0, hLr⟩)
    _ (upCascJ2OKHG_of _ _ _ _ _ _ (hU ts) (hHL ts)
      (upCascFitsOKR_of _ _ _ _ _ hvo hbase hHb (by simp [ctxOf]))) hLCw hvo hkw hhi hwfw hub
    (by simpa [ctxOf] using hsa2) hICEk hm
    (by simp [ctxOf]) hJ (hSM ts tx w hS) (fun L n hL hn hnl y hy => (hLV L n hL hn hnl y hy).1) hA hMU hCR

/-- As `SIS.Tree.delStepsCaseQd_emptyCascLHG`, for the runs of `N.Within`. -/
theorem delStepsCaseQd_emptyCascLHG (p : Params) (R : Struct BVal → Time → Prop) (hM : 2 ≤ p.M)
    (hsa2 : 2 ≤ p.splitAbove)
    (hRL : ∀ P t, R P t → RunLinksOK p P t)
    (hRP : ∀ P t, R P t → PointersOK P) (hRK : ∀ P t, R P t → KindsAllOK p P)
    (hRH : ∀ P t, R P t → HeightAllOK p P t)
    (hht : OpHtDelOKUnder p R)
    (hU : ∀ ts, UpUnlinkTreeOK (ctxOf p ts) (viewOf (treeRun p ts)))
    (hHL : ∀ ts, UpHolderLiveRunOK (ctxOf p ts) (viewOf (treeRun p ts)))
    : DelStepsCaseQd p R DelEmptyCascML := by
  intro ts tx hw hr z top hz htop ops op post hops r w hpre hI hRO hF key hop hPcL hA hMU hCR
  obtain ⟨hPc, hLCw⟩ := hPcL
  obtain ⟨pre, cv, L0, n0, hop', hm, hK, hne0, hall0, P0, hP0, hX0, hl0, _⟩ := hPc
  subst hop'
  cases hop
  obtain ⟨hvo, hkw, hbase, hHb, _, hhi, hwfw, hub⟩ := htStart_reachedU p hM R hRL hRK hRH hht ts tx hw hr z top
    hz htop ops (.del (pre ++ [cv]) :: post) hops r w hpre
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

/-- As `SIS.Tree.delStepsOK_of_open`, for the runs of `N.Within`. -/
theorem delStepsOK_of_open (p : Params) (R : Struct BVal → Time → Prop) (hM : 2 ≤ p.M)
    (hsa2 : 2 ≤ p.splitAbove)
    (hRL : ∀ P t, R P t → RunLinksOK p P t)
    (hP : ∀ ts, Within p ts → PointersOK (treeRun p ts))
    (hRK : ∀ P t, R P t → KindsAllOK p P) (hRH : ∀ P t, R P t → HeightAllOK p P t)
    (hht : OpHtDelOKUnder p R)
    (hU : ∀ ts, UpUnlinkTreeOK (ctxOf p ts) (viewOf (treeRun p ts)))
    (hHL : ∀ ts, UpHolderLiveRunOK (ctxOf p ts) (viewOf (treeRun p ts)))
    (hLC : StateOK p R (fun ts _ w => LiveCountsW p ts w)) :
    DelStepsOK p R :=
  delStepsOK_of_cases p R (delStepsCaseOK_noLeaf p R) (delStepsCaseOK_noop p R)
    (delStepsCaseOK_or p R _ _ _ delEmptyM_split (delStepsCaseOK_emptyRoom p R hM hRL hP)
      (delStepsCaseOK_or p R _ _ _ delEmptyOther_split (delStepsCaseOK_emptyRoot p R hM hsa2 hRL hP)
        (delStepsCaseOK_emptyCascLHG p R hM hsa2 hRL hP hRK hRH hht hU hHL hLC)))
    (delStepsCaseOK_room p R hM hRL hP)
    (delStepsCaseOK_fullH p R hM hsa2 hRL hP hRK hRH hht (fun ts => delFullRootStepOK_ctx p ts))

/-- As `SIS.Tree.delStepsJ2OK_of_openR`, for the runs of `N.Within`. -/
theorem delStepsJ2OK_of_openR (p : Params) (R : Struct BVal → Time → Prop)
    (S : List Tx → Tx → W → Prop) (hM : 2 ≤ p.M) (hsa2 : 2 ≤ p.splitAbove)
    (hRL : ∀ P t, R P t → RunLinksOK p P t)
    (hRP : ∀ P t, R P t → PointersOK P) (hRK : ∀ P t, R P t → KindsAllOK p P)
    (hSI : ∀ ts tx w, S ts tx w → PutInv (ctxOf p ts) (viewOf (treeRun p ts)) w)
    (hSV : ∀ ts tx w, S ts tx w → LeafVals (ctxOf p ts) (viewOf (treeRun p ts)) tx.base w)
    (hSB : ∀ ts tx w, S ts tx w → tx.base ≤ w.next)
    (hSR : ∀ ts tx w, S ts tx w →
      RangeOrder (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey)
    (hSF : ∀ ts tx w, S ts tx w →
      SegFits (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) (p.fuel - 1) w.top.rootKey)
    (hSM : ∀ ts tx w, S ts tx w → ∀ x o, w.madeFor.lookup x = some o → o < tx.base)
    (hRH : ∀ P t, R P t → HeightAllOK p P t) (hht : OpHtDelOKUnder p R)
    (hU : ∀ ts, UpUnlinkTreeOK (ctxOf p ts) (viewOf (treeRun p ts)))
    (hHL : ∀ ts, UpHolderLiveRunOK (ctxOf p ts) (viewOf (treeRun p ts)))
    (hLC : StateOK p R (fun ts _ w => LiveCountsW p ts w)) :
    DelStepsJ2OK p R S :=
  delStepsJ2OK_of_cases p R S (delStepsCaseJ2OK_noLeaf p R S hSI) (delStepsCaseJ2OK_noop p R S hSI)
    (delStepsCaseJ2OK_or p R S _ _ _ delEmptyM_split
      (delStepsCaseJ2OK_emptyRoomR p R S hM hRL hRP hRK hSI hSV hSR hSF hSM)
      (delStepsCaseJ2OK_or p R S _ _ _ delEmptyOther_split
        (delStepsCaseJ2OK_emptyRootR p R S hM hsa2 hRL hRP hRK hSI hSV hSB hSR)
        (delStepsCaseJ2OK_emptyCascRLHG p R S hM hsa2 hRL hRP hRK hSI hSV hSR hSF hSM hRH hht hU hHL
          hLC)))
    (delStepsCaseJ2OK_roomR p R S hM hRL hRP hRK hSI hSV hSB hSR hSF)
    (delStepsCaseJ2OK_fullRH p R S hM hsa2 hRL hRP hRK hSI hSV hSB hSR hSF hRH hht)

/-- As `SIS.Tree.delStepsQdL_of_openR`, for the runs of `N.Within`. -/
theorem delStepsQdL_of_openR (p : Params) (R : Struct BVal → Time → Prop) (hM : 2 ≤ p.M)
    (hsa2 : 2 ≤ p.splitAbove)
    (hRL : ∀ P t, R P t → RunLinksOK p P t)
    (hRP : ∀ P t, R P t → PointersOK P) (hRK : ∀ P t, R P t → KindsAllOK p P)
    (hRH : ∀ P t, R P t → HeightAllOK p P t)
    (hht : OpHtDelOKUnder p R)
    (hU : ∀ ts, UpUnlinkTreeOK (ctxOf p ts) (viewOf (treeRun p ts)))
    (hHL : ∀ ts, UpHolderLiveRunOK (ctxOf p ts) (viewOf (treeRun p ts))):
    DelStepsQdL p R := by
  intro ts tx hw hr z top hz htop pre op post hops r w hpre hI hRO hF key hop hmL hA hMU hCR
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
      · exact delStepsCaseQd_emptyCascLHG p R hM hsa2 hRL hRP hRK hRH hht hU hHL
          ts tx hw hr z top hz htop pre op post hops r w hpre hI hRO hF key hop (hop ▸ ⟨h2, hLCw⟩) hA hMU hCR
  · exact delStepsCaseQd_room p R hM hRL hRP hRK ts tx hw hr z top hz htop pre op post hops r w hpre hI hRO hF
      key hop (hop ▸ h) hA hMU hCR
  · exact delStepsCaseQd_fullH p R hM hsa2 hRL hRP hRK hRH hht (fun ts => delFullRootStepOK_ctx p ts)
      ts tx hw hr z top hz htop pre op post hops r w hpre hI hRO hF key hop (hop ▸ h) hA hMU hCR

/-- As `SIS.Tree.opCaseOK_of_open`, for the runs of `N.Within`. -/
theorem opCaseOK_of_open (p : Params) (R : Struct BVal → Time → Prop)
    (Q : List Tx → Op → W → W → Prop) (hQ : KeptByReads p Q)
    (C : Ctx → View BVal → W → Op → Prop)
    (h : OpCaseOK p R Q (fun c base w op => C c base w op ∧ ¬ DelNoopM c base w op ∧
      ¬ DelNoLeafM c base w op)) : OpCaseOK p R Q C :=
  opCaseOK_or p R Q C DelNoopM (fun c base w op => C c base w op ∧ ¬ DelNoopM c base w op)
    (fun c base w op hC => (Classical.em (DelNoopM c base w op)).elim Or.inl
      (fun hn => Or.inr ⟨hC, hn⟩))
    (opCaseOK_delNoop p R Q hQ)
    (opCaseOK_or p R Q _ DelNoLeafM _
      (fun c base w op hC => (Classical.em (DelNoLeafM c base w op)).elim Or.inl
        (fun hn => Or.inr ⟨hC.1, hC.2, hn⟩))
      (opCaseOK_delNoLeaf p R Q hQ) h)

/-- As `SIS.Tree.delStepsOK_of_within`, for the runs of `N.Within`. -/
theorem delStepsOK_of_within (p : Params) (R R' : Struct BVal → Time → Prop)
    (h : ∀ ts tx, Within p (ts ++ [tx]) → R (treeRun p ts) ts.length → R' (treeRun p ts) ts.length)
    (hS : DelStepsOK p R') : DelStepsOK p R :=
  fun ts tx hw hr => hS ts tx hw (h ts tx hw hr)

/-- As `SIS.Tree.heightAllOK_snocU`, for the runs of `N.Within`. -/
theorem heightAllOK_snocU (p : Params) (hM : 2 ≤ p.M) (R : Struct BVal → Time → Prop)
    (hdel : OpHtDelOKUnder p R) (ts : List Tx) (tx : Tx)
    (hw : Within p (ts ++ [tx])) (hr : R (treeRun p ts) ts.length)
    (hL : RunLinksOK p (treeRun p ts) ts.length)
    (hK : KindsAllOK p (treeRun p ts)) (hA : HeightAllOK p (treeRun p ts) ts.length) :
    HeightAllOK p (treeRun p (ts ++ [tx])) (ts.length + 1) := by
  obtain ⟨hP', hH, hN⟩ := hL
  obtain ⟨bs, w, he0⟩ := execW_success_of_within_snoc p ts tx hw
  have hfresh : ∀ q ∈ treeRun p ts, q.1 < tx.base := by
    have := (hw.w.2 ts.length (by simp)).1
    simpa using this
  have htimes : StructTimesLE (treeRun p ts) (ts.length + 1 - 1) := treeRun_timesLE p ts
  have hl := viewLinksOK_of p _ _ tx.base hfresh htimes hP' hN
  have hrun : runOps p tx.base tx.ops (ts.length + 1)
      (view (treeSpec p) (treeRun p ts) ts.length) = .ok (bs, w) := he0
  have he : execW p tx (ts.length + 1)
      (view (treeSpec p) (treeRun p ts) (ts.length + 1 - 1)) = .ok (bs, w) := hrun
  have hbook := execW_book p tx (ts.length + 1) _ bs w
    (viewIdsBelow_view p (treeRun p ts) (ts.length + 1 - 1) tx.base hfresh) he
  have hHt := execW_htCacheU p hM R hdel ts tx hw hr ⟨hP', hH, hN⟩ hK hA bs w he0
  have hA' : HeightAllOK p (treeRun p ts) (ts.length + 1 - 1) := by simpa using hA
  have hstep := heightAllOK_step p _ (ts.length + 1) tx bs w (by omega) hfresh
    htimes (treeRun_root_level p _) hH hl hP' he hbook hA' hHt
  rw [treeRun_snoc_changes p ts tx bs w hrun]
  exact hstep

/-- As `SIS.Tree.opCaseOK_of_within`, for the runs of `N.Within`. -/
theorem opCaseOK_of_within (p : Params) (R R' : Struct BVal → Time → Prop)
    (h : ∀ ts tx, Within p (ts ++ [tx]) → R (treeRun p ts) ts.length → R' (treeRun p ts) ts.length)
    (Q : List Tx → Op → W → W → Prop) (C : Ctx → View BVal → W → Op → Prop)
    (hC : OpCaseOK p R' Q C) : OpCaseOK p R Q C :=
  fun ts tx hw hr => hC ts tx hw (h ts tx hw hr)

/-- As `SIS.Tree.latestQD_snocR`, for the runs of `N.Within`. -/
theorem latestQD_snocR (p : Params) (hp : MergeParamsOK p)
    (hdel : OpHtDelOKUnder p (RunTreeQ p (LatestQD p)))
    (hT : OpCaseOK p (RunTreeQ p (LatestQD p)) (QTree p) AnyOp)
    (hPI : OpCaseOK p (RunTreeQ p (LatestQD p)) (QPutInv p) AnyOp)
    (hO : OpCaseOK p (RunTreeQ p (LatestQD p)) (QRange p) AnyOp)
    (hLv : OpCaseOK p (RunTreeQ p (LatestQD p)) (QLive p) AnyOp)
    (hDd : OpCaseOK p (RunTreeQ p (LatestQD p)) (QDead p) AnyOp) :
    ∀ ts tx, Within p (ts ++ [tx]) → RunTreeQ p (LatestQD p) (treeRun p ts) ts.length →
      RunLinksOK p (treeRun p (ts ++ [tx])) (ts.length + 1) →
      TreeAt p (treeRun p (ts ++ [tx])) (ts.length + 1) →
      LatestQD p (treeRun p (ts ++ [tx])) (ts.length + 1) := by
  intro ts tx hw hr hL' hT'
  have hM := mergeParamsOK_M p hp
  have hr0 := hr
  have hRL : ∀ P t, RunTreeQ p (LatestQD p) P t → RunLinksOK p P t := fun _ _ h => h.1
  have hRT : ∀ P t, RunTreeQ p (LatestQD p) P t → TreeAt p P t := fun _ _ h => h.2.1
  have hRI : ∀ P t, RunTreeQ p (LatestQD p) P t → InvOK p P t := fun _ _ h => h.2.2.1.1
  obtain ⟨hL, _, ⟨_, _, hK, hA, hS, hLA⟩, hD⟩ := hr
  have hD' := deadAllOK_snocR p _ hRL hRT hRI hT hPI hO hDd ts tx hw hr0 hD
  have hK' := kindsAllOK_snoc p (by omega) ts tx hw hL hK
  have hA' := heightAllOK_snocU p (by omega) _ hdel ts tx hw hr0 hL hK hA
  have hS' := sizeOK_snoc p hp ts tx hw hL hS
  have hLA' := leftAllOK_snoc p hp ts tx hw hL hLA
  exact ⟨⟨invOK_snocR p _ hRL hRT hRI hT hPI hO hLv ts tx hw hr0 hL' hT' hK' hA' hS' hLA' hD',
    hL'.1, hK', hA', hS', hLA'⟩, hD'⟩

end SIS.Tree.N
