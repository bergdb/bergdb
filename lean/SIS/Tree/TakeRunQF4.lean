/-
TP7's take-back induction itself with the merges on, on the F4 route (bergdb
024-12, for latest's top theorem): `takeBackOK_of_mergesF4`'s premises without
TP4 at every run (`hPtr`), concluding `RunTreeQ p Q` at every run within reach
(`runTree_jointJ2`'s conclusion) instead of `TakeBackOKUnder`. Case (4) takes
the run's pointers and kinds from the run premise (`opJ2Case_delMergeF4R`).
-/
import SIS.Tree.DelStepsBookK
import SIS.Tree.DelStepsUpStop
import SIS.Tree.DelStepsCascF3
import SIS.Tree.TakeDelStepsF4

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- `opJ2Case_delMergeF4` with the run's pointers and kinds from the run premise R
(`hRP`, `hRK`) instead of TP4 at every run. -/
theorem opJ2Case_delMergeF4R (p : Params) (R : Struct BVal → Time → Prop) (S : List Tx → Tx → W → Prop)
    (hS : DelStepsJ2OKF3 p R S)
    (hM : ∀ ts, MergeStepOKF3 (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1))
    (hC : ∀ ts, CollapseStepOKF4 (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1))
    (hRJ : ∀ ts B, ReplaceRootFullJ2OK (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1) B)
    (hsa2 : 2 ≤ p.splitAbove) (hcap : 1 ≤ p.mergeMax)
    (hRP : ∀ P t, R P t → PointersOK P) (hRK : ∀ P t, R P t → KindsAllOK p P) :
    OpJ2CaseOK p R S DelMergeCase := by
  have hf2 : 2 ≤ p.fuel + 1 := by unfold Params.fuel; omega
  intro ts tx hw hr z top hz htop pre op post hops r w hpre _ hSw hJ hPc
  obtain ⟨key, hop, hmerges⟩ := hPc
  have hpos : 0 < (ctxOf p ts).i := by simp [ctxOf]
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
  refine writerWP_mono (hS ts tx hw hr z top hz htop pre op post hops r w hpre hSw hJ key hop hmerges
    (fun g h v hv' => writerWP_afterDelete_delJF4 key g h (ctxOf p ts) _ (viewCoherent_ctxOf p ts)
      (p.fuel + 1) hf2 (hM ts) (hC ts) _ _ hv hk hICEk hsa2 hcap tx.base hpos (hRJ ts tx.base) w key v hv')
    (fun g h merged v hv' => writerWP_mergeUp_delJF3 key g (ctxOf p ts) _ (viewCoherent_ctxOf p ts)
      (p.fuel + 1) hf2 (hM ts) _ _ hv hk hICEk hsa2 hcap tx.base hpos w key p.fuel h merged v hv')
    (fun seg v hv' => writerWP_collapseRoot_delJF4 key seg (ctxOf p ts) _ (viewCoherent_ctxOf p ts)
      (p.fuel + 1) hf2 (hC ts) w key _ _ hv hk hICEk hsa2 tx.base hpos (hRJ ts tx.base) v hv')) ?_
  intro _ w' h' _
  exact h'

/-! ## Case (4)'s delete steps with the run's pointers and kinds from R -/

/-- `innerChildren_of_kinds` at a state that a prefix of a transaction's
operations reaches, in a run within reach, from TP4 for every run: the books
and the kinds of the overlay there by the walk (`kd_ops`), the kinds of the
structure by `treeRun_kindsAllOK`. -/
theorem innerChildren_reachedR (p : Params) (hM : 2 ≤ p.M)
    (ts : List Tx) (tx : Tx) (hPt : PointersOK (treeRun p ts)) (hKt : KindsAllOK p (treeRun p ts)) (hw : Within p (ts ++ [tx])) (top : Top)
    (pre post : List Op) (hsplit : tx.ops = pre ++ post) (r : List Bool) (w : W)
    (h : (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w))
    (hun : ∀ x, TReach (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey x →
      w.taken.contains x = false) :
    ∀ y yn cc z, TReach (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey y →
      wNode p (viewOf (treeRun p ts)) w y = some yn → yn.leaf = false →
      (cc, z) ∈ yn.liveAt (ts.length + 1) →
      ∃ m, wNode p (viewOf (treeRun p ts)) w z = some m := by
  have hwts : Within p ts := by
    have := within_take p (ts ++ [tx]) hw ts.length
    simpa using this
  have hfresh : ∀ q ∈ treeRun p ts, q.1 < tx.base := by
    have := (hw.2 ts.length (by simp)).1
    simpa using this
  have hwf : tx.wf = true := (hw.1 tx (by simp)).2
  have hkeys : ∀ op ∈ pre, keyWf op.key = true := by
    intro op hop
    unfold Tx.wf at hwf
    exact List.all_eq_true.mp hwf op (by rw [hsplit]; exact List.mem_append_left _ hop)
  have hK := hKt
  have hkd := kd_ops (kindOracleOf p (treeRun p ts)) tx.base (appendFrameOK tx.base) pre
    (ctxOf p ts) (wInit tx top)
    (viewIdsBelow_rootless _ _ (viewIdsBelow_view p (treeRun p ts) ts.length tx.base hfresh))
    (viewKinds_of p (treeRun p ts) ts.length tx.base hfresh (treeRun_timesLE p ts) hPt hK)
    (book_start _ _ top) (kdInv_start _ _ top) hM hkeys r w h
  exact innerChildren_of_kinds p (treeRun p ts) tx.base (ctxOf p ts) w rfl hK hPt hkd.1
    hkd.2.1.cache hun

/-- The kinds' context at a state between operations of a transaction within
reach: the view's ids and kinds, and the books and the kinds' books there. -/
theorem kd_contextR (p : Params) (hM : 2 ≤ p.M)
    (ts : List Tx) (tx : Tx) (hPt : PointersOK (treeRun p ts)) (hKt : KindsAllOK p (treeRun p ts)) (hw : Within p (ts ++ [tx])) (top : Top) (pre post : List Op)
    (hsplit : tx.ops = pre ++ post) (r : List Bool) (w : W)
    (h : (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w)) :
    ViewIdsBelow tx.base (ctxOf p ts).view ∧
      ViewKinds (kindOracleOf p (treeRun p ts)) tx.base (ctxOf p ts) ∧
      Book tx.base (ctxOf p ts) w ∧ KdInv (kindOracleOf p (treeRun p ts)) tx.base w := by
  have hwts : Within p ts := by
    have := within_take p (ts ++ [tx]) hw ts.length
    simpa using this
  have hfresh : ∀ q ∈ treeRun p ts, q.1 < tx.base := by
    have := (hw.2 ts.length (by simp)).1
    simpa using this
  have hwf : tx.wf = true := (hw.1 tx (by simp)).2
  have hkeys : ∀ op ∈ pre, keyWf op.key = true := by
    intro op hop
    unfold Tx.wf at hwf
    exact List.all_eq_true.mp hwf op (by rw [hsplit]; exact List.mem_append_left _ hop)
  have hK := hKt
  have hv : ViewIdsBelow tx.base (ctxOf p ts).view :=
    viewIdsBelow_rootless _ _ (viewIdsBelow_view p (treeRun p ts) ts.length tx.base hfresh)
  have hk : ViewKinds (kindOracleOf p (treeRun p ts)) tx.base (ctxOf p ts) :=
    viewKinds_of p (treeRun p ts) ts.length tx.base hfresh (treeRun_timesLE p ts) hPt hK
  have hkd := kd_ops (kindOracleOf p (treeRun p ts)) tx.base (appendFrameOK tx.base) pre
    (ctxOf p ts) (wInit tx top) hv hk (book_start _ _ top) (kdInv_start _ _ top) hM hkeys r w h
  exact ⟨hv, hk, hkd.1, hkd.2.1⟩

set_option maxHeartbeats 1600000 in
/-- The take-back of a delete that empties the leaf at the space root, the merges
on: the root's bitmap (`takeJ2_after_bitmap`), or its split when full
(`delFullRootJ2OK_ctx`). -/
theorem delStepsCaseJ2OKF3_emptyRootR (p : Params) (R : Struct BVal → Time → Prop)
    (S : List Tx → Tx → W → Prop) (hM : 2 ≤ p.M) (hsa2 : 2 ≤ p.splitAbove)
    (hRL : ∀ P t, R P t → RunLinksOK p P t)
    (hRP : ∀ P t, R P t → PointersOK P) (hRK : ∀ P t, R P t → KindsAllOK p P)
    (hSI : ∀ ts tx w, S ts tx w → PutInv (ctxOf p ts) (viewOf (treeRun p ts)) w)
    (hSV : ∀ ts tx w, S ts tx w → LeafVals (ctxOf p ts) (viewOf (treeRun p ts)) tx.base w)
    (hSB : ∀ ts tx w, S ts tx w → tx.base ≤ w.next)
    (hSR : ∀ ts tx w, S ts tx w →
      RangeOrder (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey) :
    DelStepsCaseJ2OKF3 p R S DelEmptyRootM := by
  intro ts tx hw hr z top _ htop ops op post hops r w hpre hS hJ key hop hPc _ _ _
  obtain ⟨pre, cv, L0, n0, hop', _, hK, hne0, hall0, hroot0⟩ := hPc
  subst hop'
  cases hop
  have hI := hSI ts tx w hS
  have hRO := hSR ts tx w hS
  have hkey : keyWf (pre ++ [cv]) = true := within_op_keyWf p ts tx hw ops _ post hops
  obtain ⟨rk, hrk, _⟩ := keyLeaf_rk hK
  have hB := putBase_of_run p ts tx hw (hRL _ _ hr)
  have hbook := putBook_reached p ts tx hw (hRL _ _ hr) z top htop ops r w hpre
  have hG := putInvG_of_book _ _ tx.base top w hB hbook
  have hLV := leafVals_all (hSV ts tx w hS) hkey hrk
  have hpos : 0 < (ctxOf p ts).i := by simp [ctxOf]
  obtain ⟨hv, hk, hb0, hi0⟩ := kd_contextR p hM ts tx (hRP _ _ hr) (hRK _ _ hr) hw top ops (.del (pre ++ [cv]) :: post) hops r w hpre
  have hJ0 : KdJ (ctxOf p ts) tx.base top (kindOracleOf p (treeRun p ts)) tx.base w := ⟨hbook, hb0, hi0⟩
  refine writerWP_del_toLeafMK (ctxOf p ts) _ (viewCoherent_ctxOf p ts) pre cv rk w _ hJ0
    (fun s f x v hJ hx => kdJ_descendLte _ _ tx.base top hB _ tx.base hv hk s f x v hJ hx)
    (fun s x L n v hJ hL hlk hkm => kdJ_pathAdd _ _ tx.base top hB _ tx.base hv s x L n v hJ hL hlk hkm)
    (kdJ_start _ _ tx.base top hB _ tx.base hv w hJ0) hrk (hI.pathUntaken _) hI.wf _ ?_ ?_
  · intro v hv'
    unfold fresh
    wpSimplify
    exact hv'
  · intro L n P w3 hL hn hnl hr03 hJ3 hlk3 hp3' hlinkP hXD hlkX
    obtain ⟨hne, hall, hLr⟩ := keyLeaf_all2 hK hrk
      (fun L' m => bitsUnion m.lastBitmap (m.bitsOf cv) ≠ m.lastBitmap ∧
        m.allKeysIn (bitsUnion m.lastBitmap (m.bitsOf cv)) = true ∧ L' = w.top.rootKey)
      ⟨hne0, hall0, hroot0⟩ L n hL hn hnl
    have hPnil := path_nil_of_root _ _ w hI.tree P hlinkP (by rw [hXD, hLr])
    subst hPnil
    have hp0 : (w3.path[0]?).map (·.2) = some L := by rw [hp3', hLr]; rfl
    refine writerWP_deleteUpward_rootEmpty (ctxOf p ts) L n cv (pre ++ [cv]) w3 hlk3 hp0 hnl hne hall _ ?_
    have hr03' : ReadsAs (ctxOf p ts).p (viewOf (treeRun p ts)) w
        ({ w3 with trail := "up.root-kept-empty" :: w3.trail } : W) :=
      ⟨hr03.1, hr03.2.1, hr03.2.2.1, hr03.2.2.2.1, hr03.2.2.2.2⟩
    have hJ3' : TakeJ2 (ctxOf p ts) (viewOf (treeRun p ts)) tx.base
        ({ w3 with trail := "up.root-kept-empty" :: w3.trail } : W) := takeJ2_of_readsAs _ _ _ w _ hJ hr03'
    have hLt : w.taken.contains L = false :=
      hI.pathUntaken _ (L, cv) (fromVisits_append _ _ _ pre cv _ rk hrk _ hL)
    have hcvN : ∀ y, (cv, y) ∈ n.liveAt (ctxOf p ts).i →
        wNode (ctxOf p ts).p (viewOf (treeRun p ts)) ({ w3 with trail := "up.root-kept-empty" :: w3.trail } : W) y
          = none := fun y hy => by rw [hr03'.1]; exact (hLV L n hL hn hnl y hy).1
    by_cases hroom : DelRoom (ctxOf p ts) cv n
    · refine writerWP_mono (writerWP_appendDeleteKlong_room_exactD L _ cv n _ _ hlk3 (hI.times L n hn)
        (hI.wf L n hn) hne hroom) ?_
      rintro _ v ⟨h1, h2, h3, _, _, _, h7⟩
      exact takeJ2_after_bitmap (ctxOf p ts) _ tx.base _ v cv L n hpos hJ3' hlk3
        (by show w3.taken.contains L = false; rw [hr03.2.2.1]; exact hLt) (hI.times L n hn)
        (by rw [hr03'.1, hr03'.2.1]; exact keyLeaf_reached hI hrk L hL) hcvN
        (fun y hy => by rw [hr03'.2.2.2.1]; exact (hLV L n hL hn hnl y hy).2) h1 h2 h3 h7
    · have hPOK := pathOK_of_toLeaf (ctxOf p ts) _ w ({ w3 with trail := "up.root-kept-empty" :: w3.trail } : W)
        [] n hI hr03' hp3' hlinkP hlkX
      have hNn : (wNode (ctxOf p ts).p (viewOf (treeRun p ts)) w (nodeAt w.top.rootKey [] 0)).getD
          ⟨true, []⟩ = n := by
        rw [show nodeAt w.top.rootKey [] 0 = L from hXD, hn]; rfl
      have hb3' := putBook_note "up.root-kept-empty" (ctxOf p ts) _ tx.base top hB w3 hJ3.1
      have hJ2 := delFullRootJ2OK_ctx p hsa2 ts tx.base _ (putInv_of_readsAs _ _ w _ hI hr03')
        (putInvG_of_book _ _ tx.base top _ hB hb3') (by rw [hr03'.1, hr03'.2.1]; exact hRO) hJ3'
        (by rw [hr03'.2.2.2.2]; exact hSB ts tx w hS) _ _ _ hPOK cv n hNn hnl hne hroom hcvN
      simp only [show nodeAt w.top.rootKey [] 0 = L from hXD] at hJ2
      exact writerWP_mono hJ2 (fun _ v hv' => hv'.1)

/-! ## The two obligations with the stop node's cascade named -/

/-! ## The leaf's bitmap: with room, and full -/

set_option maxHeartbeats 1600000 in
/-- The take-back of a delete whose leaf keeps a live klong and has room, on the
F3 route. -/
theorem delStepsCaseJ2OKF3_roomR (p : Params) (R : Struct BVal → Time → Prop)
    (S : List Tx → Tx → W → Prop) (hM : 2 ≤ p.M)
    (hRL : ∀ P t, R P t → RunLinksOK p P t)
    (hRP : ∀ P t, R P t → PointersOK P) (hRK : ∀ P t, R P t → KindsAllOK p P)
    (hSI : ∀ ts tx w, S ts tx w → PutInv (ctxOf p ts) (viewOf (treeRun p ts)) w)
    (hSV : ∀ ts tx w, S ts tx w → LeafVals (ctxOf p ts) (viewOf (treeRun p ts)) tx.base w)
    (hSB : ∀ ts tx w, S ts tx w → tx.base ≤ w.next)
    (hSR : ∀ ts tx w, S ts tx w →
      RangeOrder (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey)
    (hSF : ∀ ts tx w, S ts tx w →
      SegFits (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) (p.fuel - 1) w.top.rootKey) :
    DelStepsCaseJ2OKF3 p R S DelRoomM := by
  intro ts tx hw hr z top _ htop ops op post hops r w hpre hS hJ key hop hPc hA _ _
  obtain ⟨pre, cv, L0, n0, hop', _, hK, hne0, hkeep0, hroom0⟩ := hPc
  subst hop'
  cases hop
  have hI := hSI ts tx w hS
  have hRO := hSR ts tx w hS
  have hF := hSF ts tx w hS
  have hkey : keyWf (pre ++ [cv]) = true := within_op_keyWf p ts tx hw ops _ post hops
  obtain ⟨rk, hrk, hn0⟩ := keyLeaf_rk hK
  have hB := putBase_of_run p ts tx hw (hRL _ _ hr)
  have hbook := putBook_reached p ts tx hw (hRL _ _ hr) z top htop ops r w hpre
  have hICE := innerChildren_reachedR p hM ts tx (hRP _ _ hr) (hRK _ _ hr) hw top ops (.del (pre ++ [cv]) :: post) hops r w hpre
    (fun x hx => hI.untaken x (tReach_reachS _ _ _ _ hx))
  have hLV := leafVals_all (hSV ts tx w hS) hkey hrk
  obtain ⟨hv, hk, hb0, hi0⟩ := kd_contextR p hM ts tx (hRP _ _ hr) (hRK _ _ hr) hw top ops (.del (pre ++ [cv]) :: post) hops r w hpre
  have hJ0 : KdJ (ctxOf p ts) tx.base top (kindOracleOf p (treeRun p ts)) tx.base w := ⟨hbook, hb0, hi0⟩
  refine writerWP_del_toLeafMK (ctxOf p ts) _ (viewCoherent_ctxOf p ts) pre cv rk w _ hJ0
    (fun s f x v hJ hx => kdJ_descendLte _ _ tx.base top hB _ tx.base hv hk s f x v hJ hx)
    (fun s x L n v hJ hL hlk hkm => kdJ_pathAdd _ _ tx.base top hB _ tx.base hv s x L n v hJ hL hlk hkm)
    (kdJ_start _ _ tx.base top hB _ tx.base hv w hJ0) hrk (hI.pathUntaken _) hI.wf _ ?_ ?_
  · intro v hv'
    unfold fresh
    wpSimplify
    exact hv'
  · intro L n P w3 hL hn hnl hr03 hJ3 hlk3 hp3' _ hXD _
    obtain ⟨hwf, htimes, hne, hkeep, hroomD⟩ := keyLeaf_all hK hrk
      (fun m => klongsWf m.ks = true ∧ (∀ s, Klong.time s ∈ m.ks → s ≤ (ctxOf p ts).i) ∧
        bitsUnion m.lastBitmap (m.bitsOf cv) ≠ m.lastBitmap ∧
        m.allKeysIn (bitsUnion m.lastBitmap (m.bitsOf cv)) = false ∧ DelRoom (ctxOf p ts) cv m)
      ⟨hI.wf L0 n0 hn0, hI.times L0 n0 hn0, hne0, hkeep0, hroom0⟩ L n hL hn hnl
    have hLt : w.taken.contains L = false :=
      hI.pathUntaken _ (L, cv) (fromVisits_append _ _ _ pre cv _ rk hrk _ hL)
    obtain ⟨a, hpx⟩ := path_last_of_toLeaf w w3 P L hp3' hXD
    have hJ23 : TakeJ2 (ctxOf p ts) (viewOf (treeRun p ts)) tx.base w3 := takeJ2_of_readsAs _ _ _ w w3 hJ hr03
    refine writerWP_deleteUpward_full (ctxOf p ts) L n P.length cv (pre ++ [cv]) w3 hlk3 hne hkeep
      (fun v => DelInvJF3 (ctxOf p ts) (viewOf (treeRun p ts)) w (pre ++ [cv]) (p.fuel + 1)
        (kindOracleOf p (treeRun p ts)) tx.base tx.base v) _ ?_ ?_
    · refine writerWP_mono (writerWP_and (writerWP_and
        (writerWP_appendDeleteKlong_room_exactD L _ cv n _ _ hlk3 htimes hwf hne hroomD)
        (putBook_appendDeleteKlong L _ cv _ _ tx.base top hB _ hJ3.1))
        (kd_appendDeleteKlong _ tx.base L P.length cv _ w3 hv hk hJ3.2.1 hJ3.2.2 a hpx)) ?_
      rintro _ v ⟨⟨⟨h1, h2, h3, _, h5, _, h7⟩, hbv⟩, hkv⟩
      refine ⟨⟨delInvF_after_bitmap (ctxOf p ts) _ tx.base top hB w w3 v pre cv rk L n hI hRO hICE hF
        hkey hrk hL hn hnl hr03 hLt h1 h2 h3 h7 hbv, hkv.1, hkv.2.1⟩, ?_, ?_⟩
      · exact takeJ2_after_bitmap (ctxOf p ts) _ tx.base w3 v cv L n (by simp [ctxOf]) hJ23 hlk3
          (by rw [hr03.2.2.1]; exact hLt) (hI.times L n hn)
          (by rw [hr03.1, hr03.2.1]; exact keyLeaf_reached hI hrk L hL)
          (fun y hy => by rw [hr03.1]; exact (hLV L n hL hn hnl y hy).1)
          (fun y hy => by rw [hr03.2.2.2.1]; exact (hLV L n hL hn hnl y hy).2) h1 h2 h3 h7
      · rw [h5, hr03.2.2.2.2]; exact hSB ts tx w hS
    · intro g h v hv'
      exact writerWP_mono (hA g h v hv') (fun _ v' hv'' => hv''.2.1)

/-! ## The upward delete with room -/

/-- The take-back of a delete whose leaf empties, the upward delete with room,
on the F3 route. -/
theorem delStepsCaseJ2OKF3_emptyRoomR (p : Params) (R : Struct BVal → Time → Prop)
    (S : List Tx → Tx → W → Prop) (hM : 2 ≤ p.M)
    (hRL : ∀ P t, R P t → RunLinksOK p P t)
    (hRP : ∀ P t, R P t → PointersOK P) (hRK : ∀ P t, R P t → KindsAllOK p P)
    (hSI : ∀ ts tx w, S ts tx w → PutInv (ctxOf p ts) (viewOf (treeRun p ts)) w)
    (hSV : ∀ ts tx w, S ts tx w → LeafVals (ctxOf p ts) (viewOf (treeRun p ts)) tx.base w)
    (hSR : ∀ ts tx w, S ts tx w →
      RangeOrder (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey)
    (hSF : ∀ ts tx w, S ts tx w →
      SegFits (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) (p.fuel - 1) w.top.rootKey)
    (hSM : ∀ ts tx w, S ts tx w → ∀ x o, w.madeFor.lookup x = some o → o < tx.base) :
    DelStepsCaseJ2OKF3 p R S DelEmptyRoomM := by
  intro ts tx hw hr z top _ htop ops op post hops r w hpre hS hJ key hop hPc hA hMU hCR
  obtain ⟨pre, cv, L0, n0, hop', hm, hK, hne0, hall0, hup0⟩ := hPc
  subst hop'
  cases hop
  have hI := hSI ts tx w hS
  have hkey : keyWf (pre ++ [cv]) = true := within_op_keyWf p ts tx hw ops _ post hops
  obtain ⟨rk, hrk, _⟩ := keyLeaf_rk hK
  have hB := putBase_of_run p ts tx hw (hRL _ _ hr)
  have hbook := putBook_reached p ts tx hw (hRL _ _ hr) z top htop ops r w hpre
  have hICE := innerChildren_reachedR p hM ts tx (hRP _ _ hr) (hRK _ _ hr) hw top ops (.del (pre ++ [cv]) :: post) hops r w hpre
    (fun x hx => hI.untaken x (tReach_reachS _ _ _ _ hx))
  have hLV := leafVals_all (hSV ts tx w hS) hkey hrk
  obtain ⟨hv, hk, hb0, hi0⟩ := kd_contextR p hM ts tx (hRP _ _ hr) (hRK _ _ hr) hw top ops (.del (pre ++ [cv]) :: post) hops r w hpre
  exact writerWP_del_emptyRoomMJK (ctxOf p ts) _ (viewCoherent_ctxOf p ts) pre cv rk w tx.base top hB hbook
    _ tx.base hv hk hb0 hi0
    hI (hSR ts tx w hS) (hSF ts tx w hS) hICE hkey hrk (keyLeaf_all2 hK hrk _ ⟨hne0, hall0, hup0⟩) hm
    (by simp [ctxOf]) hJ (hSM ts tx w hS) (fun L n hL hn hnl y hy => (hLV L n hL hn hnl y hy).1) hA hMU hCR

/-! ## The case on the F3/F4 route -/

/-! ## The take-back's state between operations with the fuel and the replaced ids -/

/-- `TakeS3` with the state fitting the fuel (`SegFits`) and the ids that
`madeFor` names below the transaction's first id: the state between a
transaction's operations that `DelStepsJ2OKF3`'s S inputs `hSF` and `hSM` ask
for. -/
def TakeS4 (p : Params) (ts : List Tx) (tx : Tx) (w : W) : Prop :=
  TakeS3 p ts tx w ∧
    SegFits (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) (p.fuel - 1) w.top.rootKey ∧
    ∀ x o, w.madeFor.lookup x = some o → o < tx.base

/-- `runTreeQ_of_cases3` with `TakeS4`, its two extra parts from `StateOK` inputs. -/
theorem runTreeQ_of_cases3S (p : Params) (hM : 2 ≤ p.M) (hsa : 2 ≤ p.splitAbove)
    (Q : Struct BVal → Time → Prop) (hQ0 : Q (initStruct p) 0)
    (hQs : ∀ ts tx, Within p (ts ++ [tx]) → RunTreeQ p Q (treeRun p ts) ts.length →
      RunLinksOK p (treeRun p (ts ++ [tx])) (ts.length + 1) →
      TreeAt p (treeRun p (ts ++ [tx])) (ts.length + 1) →
      Q (treeRun p (ts ++ [tx])) (ts.length + 1))
    (hQP : ∀ P t, Q P t → PointersOK P) (hQK : ∀ P t, Q P t → KindsAllOK p P)
    (ho : OpTreeOKUnder p (RunTreeQ p Q))
    (hPI : StateOK p (RunTreeQ p Q) (fun ts _ w => PutInv (ctxOf p ts) (viewOf (treeRun p ts)) w))
    (hRO : StateOK p (RunTreeQ p Q) (fun ts _ w =>
      RangeOrder (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey))
    (hB : BaseStartOK p (RunTreeQ p Q))
    (hFS : StateOK p (RunTreeQ p Q) (fun ts _ w =>
      SegFits (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) (p.fuel - 1) w.top.rootKey))
    (hMF : StateOK p (RunTreeQ p Q) (fun _ tx w => ∀ x o, w.madeFor.lookup x = some o → o < tx.base))
    (c3 : OpJ2CaseOK p (RunTreeQ p Q) (TakeS4 p) PutNewSegFullCase)
    (c4 : OpJ2CaseOK p (RunTreeQ p Q) (TakeS4 p) DelMergeCase)
    (c7 : OpJ2CaseOK p (RunTreeQ p Q) (TakeS4 p) DelEmptyCase)
    (c9 : OpJ2CaseOK p (RunTreeQ p Q) (TakeS4 p) DelFullCase) :
    ∀ ts, Within p ts → RunTreeQ p Q (treeRun p ts) ts.length := by
  have hSI : ∀ ts tx w, TakeS4 p ts tx w → PutInv (ctxOf p ts) (viewOf (treeRun p ts)) w :=
    fun _ _ _ h => h.1.1.1.1
  have hSV : ∀ ts tx w, TakeS4 p ts tx w → LeafVals (ctxOf p ts) (viewOf (treeRun p ts)) tx.base w :=
    fun _ _ _ h => h.1.1.1.2
  have hSB : ∀ ts tx w, TakeS4 p ts tx w → tx.base ≤ w.next := fun _ _ _ h => h.1.1.2
  have hSR : ∀ ts tx w, TakeS4 p ts tx w →
      RangeOrder (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey := fun _ _ _ h => h.1.2
  have hS : StateOK p (RunTreeQ p Q) (TakeS4 p) := by
    intro ts tx hw hr z top hz htop pre post hsplit r w h
    exact ⟨⟨⟨⟨hPI ts tx hw hr z top hz htop pre post hsplit r w h,
      leafVals_reached p hM ts tx hw top pre post hsplit r w h (hQP _ _ hr.2.2) (hQK _ _ hr.2.2)⟩,
      base_le_next_reached p hM ts tx hw top pre post hsplit r w h (hQP _ _ hr.2.2) (hQK _ _ hr.2.2)⟩,
      hRO ts tx hw hr z top hz htop pre post hsplit r w h⟩,
      hFS ts tx hw hr z top hz htop pre post hsplit r w h, hMF ts tx hw hr z top hz htop pre post hsplit r w h⟩
  have hSRF : ∀ ts tx w, TakeS4 p ts tx w → ReachedFree p (treeRun p ts) (ts.length + 1) w :=
    fun ts _ w h y hy => h.1.1.1.1.untaken y (tReach_reachS _ _ _ _ hy)
  have hO : OpJ2OK p (RunTreeQ p Q) (TakeS4 p) :=
    opJ2OK_of_cases p _ _ (opJ2Case_putLeafRoom p _ _ hSI hSV)
      (opJ2Case_putLeafFull p _ _ (fun _ _ h => h.1) hsa hSI hSV hSB hSR)
      (opJ2Case_putNewSeg p _ _ hM hSI hSB c3) c4
      (opJ2Case_delNoLeaf p _ _ hSI) (opJ2Case_delNoop p _ _ hSI) c7 (opJ2Case_delRoom p _ _ hSI hSV) c9
  exact runTree_jointJ2 p hM Q hQ0 hQs ho (TakeS4 p) hO hS hSRF hB
    (takenNotValOK_of p hM _ (fun _ _ h => hQP _ _ h.2.2) (fun _ _ h => hQK _ _ h.2.2))

/-- `runTreeQ_of_cases4` with `TakeS4`. -/
theorem runTreeQ_of_cases4S (p : Params) (hM : 2 ≤ p.M) (hsa : 2 ≤ p.splitAbove)
    (Q : Struct BVal → Time → Prop) (hQ0 : Q (initStruct p) 0)
    (hQs : ∀ ts tx, Within p (ts ++ [tx]) → RunTreeQ p Q (treeRun p ts) ts.length →
      RunLinksOK p (treeRun p (ts ++ [tx])) (ts.length + 1) →
      TreeAt p (treeRun p (ts ++ [tx])) (ts.length + 1) →
      Q (treeRun p (ts ++ [tx])) (ts.length + 1))
    (hQP : ∀ P t, Q P t → PointersOK P) (hQK : ∀ P t, Q P t → KindsAllOK p P)
    (ho : OpTreeOKUnder p (RunTreeQ p Q))
    (hPI : StateOK p (RunTreeQ p Q) (fun ts _ w => PutInv (ctxOf p ts) (viewOf (treeRun p ts)) w))
    (hRO : StateOK p (RunTreeQ p Q) (fun ts _ w =>
      RangeOrder (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey))
    (hB : BaseStartOK p (RunTreeQ p Q))
    (hFS : StateOK p (RunTreeQ p Q) (fun ts _ w =>
      SegFits (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) (p.fuel - 1) w.top.rootKey))
    (hMF : StateOK p (RunTreeQ p Q) (fun _ tx w => ∀ x o, w.madeFor.lookup x = some o → o < tx.base))
    (c4 : OpJ2CaseOK p (RunTreeQ p Q) (TakeS4 p) DelMergeCase)
    (c7 : OpJ2CaseOK p (RunTreeQ p Q) (TakeS4 p) DelEmptyCase)
    (c9 : OpJ2CaseOK p (RunTreeQ p Q) (TakeS4 p) DelFullCase) :
    ∀ ts, Within p ts → RunTreeQ p Q (treeRun p ts) ts.length :=
  runTreeQ_of_cases3S p hM hsa Q hQ0 hQs hQP hQK ho hPI hRO hB hFS hMF
    (opJ2Case_putNewSegFull p _ _ (fun _ _ h => h.1) hM hsa (fun _ _ _ h => h.1.1.1.1)
      (fun _ _ _ h => h.1.1.2) (fun _ _ _ h => h.1.2)) c4 c7 c9

/-- `runTreeQ_of_cases_merges4` with `TakeS4`. -/
theorem runTreeQ_of_cases_merges4S (p : Params) (hM : 2 ≤ p.M) (hsa : 2 ≤ p.splitAbove)
    (hm : p.merges = true) (Q : Struct BVal → Time → Prop) (hQ0 : Q (initStruct p) 0)
    (hQs : ∀ ts tx, Within p (ts ++ [tx]) → RunTreeQ p Q (treeRun p ts) ts.length →
      RunLinksOK p (treeRun p (ts ++ [tx])) (ts.length + 1) →
      TreeAt p (treeRun p (ts ++ [tx])) (ts.length + 1) →
      Q (treeRun p (ts ++ [tx])) (ts.length + 1))
    (hQP : ∀ P t, Q P t → PointersOK P) (hQK : ∀ P t, Q P t → KindsAllOK p P)
    (ho : OpTreeOKUnder p (RunTreeQ p Q))
    (hPI : StateOK p (RunTreeQ p Q) (fun ts _ w => PutInv (ctxOf p ts) (viewOf (treeRun p ts)) w))
    (hRO : StateOK p (RunTreeQ p Q) (fun ts _ w =>
      RangeOrder (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey))
    (hB : BaseStartOK p (RunTreeQ p Q))
    (hFS : StateOK p (RunTreeQ p Q) (fun ts _ w =>
      SegFits (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) (p.fuel - 1) w.top.rootKey))
    (hMF : StateOK p (RunTreeQ p Q) (fun _ tx w => ∀ x o, w.madeFor.lookup x = some o → o < tx.base))
    (c4 : OpJ2CaseOK p (RunTreeQ p Q) (TakeS4 p) DelMergeCase) :
    ∀ ts, Within p ts → RunTreeQ p Q (treeRun p ts) ts.length :=
  runTreeQ_of_cases4S p hM hsa Q hQ0 hQs hQP hQK ho hPI hRO hB hFS hMF c4
    (opJ2CaseOK_void p _ _ _ hm delEmptyCase_merges) (opJ2CaseOK_void p _ _ _ hm delFullCase_merges)

/-- `runTreeQ_of_mergesF4` with `TakeS4` for `DelStepsJ2OKF3`'s S: the state
fits the fuel and the replaced ids are below the transaction's first id at
every state between operations (`hFS`, `hMF`). -/
theorem runTreeQ_of_mergesF4S (p : Params) (hM : 2 ≤ p.M) (hsa : 2 ≤ p.splitAbove)
    (hcap : 1 ≤ p.mergeMax) (hm : p.merges = true)
    (Q : Struct BVal → Time → Prop) (hQ0 : Q (initStruct p) 0)
    (hQs : ∀ ts tx, Within p (ts ++ [tx]) → RunTreeQ p Q (treeRun p ts) ts.length →
      RunLinksOK p (treeRun p (ts ++ [tx])) (ts.length + 1) →
      TreeAt p (treeRun p (ts ++ [tx])) (ts.length + 1) →
      Q (treeRun p (ts ++ [tx])) (ts.length + 1))
    (hQP : ∀ P t, Q P t → PointersOK P) (hQK : ∀ P t, Q P t → KindsAllOK p P)
    (ho : OpTreeOKUnder p (RunTreeQ p Q))
    (hPI : StateOK p (RunTreeQ p Q) (fun ts _ w => PutInv (ctxOf p ts) (viewOf (treeRun p ts)) w))
    (hRO : StateOK p (RunTreeQ p Q) (fun ts _ w =>
      RangeOrder (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey))
    (hFS : StateOK p (RunTreeQ p Q) (fun ts _ w =>
      SegFits (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) (p.fuel - 1) w.top.rootKey))
    (hMF : StateOK p (RunTreeQ p Q) (fun _ tx w => ∀ x o, w.madeFor.lookup x = some o → o < tx.base))
    (hDS : DelStepsJ2OKF3 p (RunTreeQ p Q) (TakeS4 p))
    (hMS : ∀ ts, MergeStepOKF3 (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1))
    (hCo : ∀ ts, CollapseStepOKF4 (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1))
    (hRJ : ∀ ts B, ReplaceRootFullJ2OK (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1) B) :
    ∀ ts, Within p ts → RunTreeQ p Q (treeRun p ts) ts.length :=
  runTreeQ_of_cases_merges4S p hM hsa hm Q hQ0 hQs hQP hQK ho hPI hRO (baseStartOK_runTreeQ p Q) hFS hMF
    (opJ2Case_delMergeF4R p _ _ hDS hMS hCo hRJ hsa hcap (fun _ _ h => hQP _ _ h.2.2) (fun _ _ h => hQK _ _ h.2.2))

end SIS.Tree
