/-
The delete side of the heights' walk at the runs a predicate R holds of
(bergdb 024-22, step 4; for latest's run induction, which proves TP4 and the
kinds at the run it is at): `OpHtDelOKUnder p R` is `OpHtDelOK p` asked only
at the runs `R (treeRun p ts) ts.length`. From the delete's checks but the
path's at such runs, with R giving TP4 and the kinds
(`opHtDelOKUnder_of_chk2`, by putinv's `kd_contextR`); from `OpHtDelOK`
(`opHtDelOKUnder_of`). Its uses, as HeightsRun.lean's and HeightsFit.lean's
with R: `ht_reachedU`, `execW_htCacheU`, `takeBelowFuelOK_of_delHU`,
`txSegFitsOK_of_takeBelowDelRHU`, and `txSegFitsOK_of_takeBelowDelR2U` from
`OpDelChk2OK`. At an operation's start the heights' context with every node not
taken back below the fuel (`htStart_reachedU`, the doomed transaction).
-/
import SIS.Tree.HeightsPathFree
import SIS.Tree.TakeRunQF4

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- `OpHtDelOK` at the runs R holds of. -/
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

/-- `OpHtDelOK` at every run gives it at the runs R holds of. -/
theorem opHtDelOKUnder_of (p : Params) (R : Struct BVal → Time → Prop) (h : OpHtDelOK p) :
    OpHtDelOKUnder p R :=
  fun ts tx hw _ => h ts tx hw

/-- The delete side of the walk at the runs R holds of, from the delete's checks
but the path's, R giving TP4 and the kinds. -/
theorem opHtDelOKUnder_of_chk2 (p : Params) (hM : 2 ≤ p.M) (R : Struct BVal → Time → Prop)
    (hRP : ∀ P t, R P t → PointersOK P) (hRK : ∀ P t, R P t → KindsAllOK p P)
    (h : OpDelChk2OK p) : OpHtDelOKUnder p R := by
  intro ts tx hw hr z top hz htop pre key post hsplit r w hpre hvo hkw hb hwf hi r' v he
  obtain ⟨-, hk, -, hki⟩ := kd_contextR p hM ts tx (hRP _ _ hr) (hRK _ _ hr) hw top pre
    (Op.del key :: post) hsplit r w hpre
  exact (ht_putKvDelChk2 tx.base key (ctxOf p ts) w hvo (by simp [ctxOf]) hkw hb hi hwf hk hki
    (by simpa [ctxOf] using hM) r' v
    (h ts tx hw z top hz htop pre key post hsplit r w hpre r' v he)).2.1

/-- `ht_reached` with the delete side of the walk at the runs R holds of. -/
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

/-- `execW_htCache` with the delete side of the walk at the runs R holds of. -/
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

/-- `takeBelowFuelOK_of_del` from the delete side of the heights' walk at the
runs R holds of (`OpHtDelOKUnder`) in place of `OpDelChkOK`: a put takes nothing back (`ht_putKv_put`'s `HtLe`). -/
theorem takeBelowFuelOK_of_delHU (p : Params) (hM : 2 ≤ p.M) (R : Struct BVal → Time → Prop)
    (hRL : ∀ P t, R P t → RunLinksOK p P t) (hRK : ∀ P t, R P t → KindsAllOK p P)
    (hRH : ∀ P t, R P t → HeightAllOK p P t) (hht : OpHtDelOKUnder p R)
    (hdel : TakeBelowFuelDelOK p) :
    ∀ ts tx, Within p (ts ++ [tx]) → R (treeRun p ts) ts.length → ∀ z top,
      lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z →
      topOf p (ctxOf p ts).view z = .ok top →
      ∀ pre op post, tx.ops = pre ++ op :: post →
      ∀ r w, (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
      ∀ a v, putKv op (ctxOf p ts) w = .ok (a, v) →
      ∀ x g h, (x, g, h) ∈ w.gh → w.taken.contains x = false → v.taken.contains x = true →
        h < p.fuel := by
  intro ts tx hw hr z top hz htop pre op post hsplit r w hpre a v he x g h hm hx hv
  cases op with
  | del key => exact hdel ts tx hw z top hz htop pre key post hsplit r w hpre a v he x g h hm hx hv
  | put key hv0 =>
    exfalso
    have hR := hRL _ _ hr
    have hvo := viewHtOK_of_run p ts tx hw hR (hRK _ _ hr) (hRH _ _ hr)
    have hi := ht_reachedU p hM R hht ts tx hw hr hR hvo z top hz htop pre
      (Op.put key hv0 :: post) hsplit r w hpre
    have hbk := putBook_reached p ts tx hw hR z top htop pre r w hpre
    have hB := putBase_of_run p ts tx hw hR
    have := (ht_putKv_put tx.base (appendFrameOK tx.base) key hv0 (ctxOf p ts) w hvo
      (by simp [ctxOf]) hbk.book hi hM hB.wf hbk.klongs a v he).2.2.2
    rw [this, hx] at hv
    cases hv

/-- Every cached height of a node not taken back is at most b. -/
def UntakenBound (b : Nat) (v : W) : Prop :=
  ∀ x g h, (x, g, h) ∈ v.gh → v.taken.contains x = false → h ≤ b

set_option maxHeartbeats 1600000 in
/-- At a state that a transaction's earlier operations reach, at the runs R
holds of: the heights' context and the facts `htJ_start` asks, the bound below
the fuel by the doomed transaction (as in `txSegFitsOK_of_takeBelowDelRHU`). -/
theorem htStart_reachedU (p : Params) (hM : 2 ≤ p.M) (R : Struct BVal → Time → Prop)
    (hRL : ∀ P t, R P t → RunLinksOK p P t) (hRK : ∀ P t, R P t → KindsAllOK p P)
    (hRH : ∀ P t, R P t → HeightAllOK p P t) (hht : OpHtDelOKUnder p R)
    (hdel : TakeBelowFuelDelOK p) (ts : List Tx) (tx : Tx) (hw : Within p (ts ++ [tx]))
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
  have htb := takeBelowFuelOK_of_delHU p hM R hRL hRK hRH hht hdel ts tx hw hr z top hz htop
  have hR := hRL _ _ hr
  have hK := hRK _ _ hr
  have hA := hRH _ _ hr
  have hvo := viewHtOK_of_run p ts tx hw hR hK hA
  have hi := ht_reachedU p hM R hht ts tx hw hr hR hvo z top hz htop pre post
    hsplit r w hpre
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

set_option maxHeartbeats 1600000 in
/-- `txSegFitsOK_of_takeBelowDelR` from the delete side of the heights' walk at
the runs R holds of (`OpHtDelOKUnder`) in place of `OpDelChkOK`. -/
theorem txSegFitsOK_of_takeBelowDelRHU (p : Params) (hM : 2 ≤ p.M) (R : Struct BVal → Time → Prop)
    (hRL : ∀ P t, R P t → RunLinksOK p P t) (hRK : ∀ P t, R P t → KindsAllOK p P)
    (hRH : ∀ P t, R P t → HeightAllOK p P t) (hht : OpHtDelOKUnder p R)
    (hdel : TakeBelowFuelDelOK p) : TxSegFitsOK p R := by
  intro ts tx hw hr z top hz htop pre post hsplit r w hpre
  obtain ⟨hvo, -, hbase, hHb, hbk, hi, -, hub⟩ := htStart_reachedU p hM R hRL hRK hRH hht hdel
    ts tx hw hr z top hz htop pre post hsplit r w hpre
  refine segFits_of_heightsU hbk hi.cache hvo.heights _ hbase (p.fuel - 1) _ ?_
  intro x n hn h hh
  rcases hh with ⟨g, hm⟩ | hh
  · exact hub x g h hm (ht_wNode_cases hn).1
  · have := hHb x h hh
    have := fuel_gt_H p
    omega

/-- TP10's fuel premise between operations (`TxSegFitsOK`, latest's `hfit`),
from the delete's checks but the path's and the deletes' take-backs below the
fuel, with TP4 and the kinds from R. -/
theorem txSegFitsOK_of_takeBelowDelR2U (p : Params) (hM : 2 ≤ p.M)
    (R : Struct BVal → Time → Prop) (hRP : ∀ P t, R P t → PointersOK P)
    (hRL : ∀ P t, R P t → RunLinksOK p P t) (hRK : ∀ P t, R P t → KindsAllOK p P)
    (hRH : ∀ P t, R P t → HeightAllOK p P t) (hchk : OpDelChk2OK p)
    (hdel : TakeBelowFuelDelOK p) : TxSegFitsOK p R :=
  txSegFitsOK_of_takeBelowDelRHU p hM R hRL hRK hRH (opHtDelOKUnder_of_chk2 p hM R hRP hRK hchk)
    hdel

end SIS.Tree
