/-
The delete into a full leaf with the fuel after its split proved (bergdb 024-12,
cost's `DelFullFitsOKR`): the delete's walk to its leaf carries the heights'
invariant (`KdHtJ`, `writerWP_del_toLeafMKH`) from the operation's start
(`htStart_reachedU`), so the fuel after the split is no longer a premise.
-/
import SIS.Tree.DelStepsUnlinkTree
import SIS.Tree.DelStepsKdH
import SIS.Tree.HeightsFitsR

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

set_option maxHeartbeats 1600000 in
/-- The delete's invariant with the kinds' books (`DelInv`) after the bitmap
into a full leaf at the walk's end, from the state w between operations: the
reading's facts (`writerWP_appendDeleteKlong_full_inv_any`), the fuel premise
after the split, the books, and the inner children from the kinds. -/
theorem writerWP_appendDeleteKlong_full_delH (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (KO : KindOracle) (BK : NodeId)
    (hRoot : DelFullRootStepOK c base) (H : NodeId → Nat → Prop)
    (hFits : DelFullFitsOKR c base H BK) (hsa2 : 2 ≤ c.p.splitAbove)
    (hv : ViewIdsBelow BK c.view) (hk : ViewKinds KO BK c)
    (hICEk : ICEFromKinds c base KO BK)
    (w : W) (pre : List Nat) (cv : Nat) (rk B : NodeId) (top0 : Top)
    (hB : PutBase c base B) (hI : PutInv c base w) (hRO : RangeOrder (wNode c.p base w) c.i w.top.rootKey)
    (hF : SegFits (wNode c.p base w) c.i (c.p.fuel - 1) w.top.rootKey) (hkey : keyWf (pre ++ [cv]) = true)
    (hrk : segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk)
    (L : NodeId) (n : KNode) (P : List (Option Nat × NodeId)) (w3 : W)
    (hL : (L, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk) (hn : wNode c.p base w L = some n)
    (hnl : n.leaf = true) (hne : bitsUnion n.lastBitmap (n.bitsOf cv) ≠ n.lastBitmap)
    (hfull : ¬ DelRoom c cv n)
    (hr03 : ReadsAs c.p base w w3) (hJ3 : KdJ c B top0 KO BK w3) (hH3 : HtJ c H BK w3)
    (hp3' : w3.path = (none, w.top.rootKey) :: P)
    (hlinkP : LinkedFrom (wNode c.p base w) c.i w.top.rootKey P)
    (hXD : nodeAt w.top.rootKey P P.length = L)
    (hlkX : ∀ i, i ≤ P.length → w3.nodes.lookup (nodeAt w.top.rootKey P i) =
      some ((wNode c.p base w (nodeAt w.top.rootKey P i)).getD n)) :
    WriterWP (appendDeleteKlong L P.length cv) c w3
      (fun _ v => DelInv c base w (pre ++ [cv]) (c.p.fuel + 1) KO BK v) := by
  have hPOK := pathOK_of_toLeaf c base w w3 P n hI hr03 hp3' hlinkP hlkX
  have hNn : (wNode c.p base w (nodeAt w.top.rootKey P P.length)).getD ⟨true, []⟩ = n := by
    rw [hXD, hn]; rfl
  have hI3 := putInv_of_readsAs c base w w3 hI hr03
  have hG3 := putInvG_of_book c base B top0 w3 hB hJ3.1
  have hRO3 : RangeOrder (wNode c.p base w3) c.i w3.top.rootKey := by rw [hr03.1, hr03.2.1]; exact hRO
  have hF3 : SegFits (wNode c.p base w3) c.i (c.p.fuel - 1) w3.top.rootKey := by
    rw [hr03.1, hr03.2.1]; exact hF
  obtain ⟨a, hpx⟩ := path_last_of_toLeaf w w3 P L hp3' hXD
  have hinv := writerWP_appendDeleteKlong_full_inv_any c base hvc hRoot w3 hI3 hG3 hRO3 hF3 hsa2 P.length _ _ _
    hPOK pre cv rk hkey (by rw [hr03.1, hr03.2.1]; exact hrk)
    (by show (nodeAt w.top.rootKey P P.length, cv) ∈ _; rw [hXD, hr03.1]; exact hL)
    (by rw [hr03.1, hr03.2.1]; exact hI.keyUniq pre cv rk hkey hrk)
    (by rw [hNn]; exact hnl) (by rw [hNn]; exact hne) (by rw [hNn]; exact hfull)
  have hfit := hFits w3 hI3 hF3 P.length _ _ _ hPOK cv (by rw [hNn]; exact hnl) (by rw [hNn]; exact hne)
    (by rw [hNn]; exact hfull) hH3 (by rw [hp3']; simp)
  simp only [hXD] at hinv hfit
  refine writerWP_mono (writerWP_and (writerWP_and (writerWP_and hinv hfit)
    (putBook_appendDeleteKlong L _ cv c base B top0 hB w3 hJ3.1))
    (kd_appendDeleteKlong KO BK L P.length cv c w3 hv hk hJ3.2.1 hJ3.2.2 a hpx)) ?_
  rintro _ v ⟨⟨⟨⟨hTv, htv, hvv, hnv, hreachv, hRv, hreadv⟩, hFv⟩, hbv⟩, hbk, hik, _⟩
  have hun : ∀ y, TReach (wNode c.p base v) c.i v.top.rootKey y → v.taken.contains y = false := by
    intro y hy
    rw [htv]
    rcases hreachv y hy with h | h
    · exact hI3.untaken y (tReach_reachS _ _ _ _ h)
    · cases h' : w3.taken.contains y with
      | false => rfl
      | true => have := hI3.ids.2.2.1 y h'; omega
  obtain ⟨hPv, hGv⟩ := putInv_after_step c base v B top0 hB hbv hTv
    (fun y hy => hun y (reachS_tReach _ _ _ _ hy)) hRv
  refine ⟨⟨hPv, hGv, hRv, hICEk v hbk hik hun, by simpa using hFv, fun key' hk' => ?_, B, top0, hB, hbv⟩,
    hbk, hik⟩
  rw [hreadv hFv key' hk']
  have hw3w : wGetAt c.p c.i base w3 (c.p.fuel + 1) key' = wGetAt c.p c.i base w (c.p.fuel + 1) key' := by
    unfold wGetAt
    rw [hr03.1, hr03.2.1, ReadsAs.value _ _ _ _ hr03]
  rw [hw3w]

/-- The reading of a delete into a full leaf, the merges on:
from the fuel premise after the split (cost's step 4) and the
leaf at the space root (`DelFullRootStepOK`), for runs with their links and
TP4 at every run, 2 ≤ splitAbove. -/
theorem delStepsCaseOK_fullHG (p : Params) (R : Struct BVal → Time → Prop) (hM : 2 ≤ p.M)
    (hsa2 : 2 ≤ p.splitAbove)
    (hRL : ∀ P t, R P t → RunLinksOK p P t)
    (hP : ∀ ts, Within p ts → PointersOK (treeRun p ts))
    (hRK : ∀ P t, R P t → KindsAllOK p P) (hRH : ∀ P t, R P t → HeightAllOK p P t)
    (hht : OpHtDelOKUnder p R) (hdel : TakeBelowFuelDelOK p)
    (hRoot : ∀ ts, DelFullRootStepOK (ctxOf p ts) (viewOf (treeRun p ts)))
    (I : List Tx → Tx → W → Key → W → Prop) : DelStepsCaseOKG p R DelFullM I := by
  intro ts tx hw hr z top hz htop ops op post hops r w hpre hI hRO hF key hop hPc hin hout hA _ _
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
  obtain ⟨hvo, hkw, _, _, _, hhi, hwfw, hub⟩ := htStart_reachedU p hM R hRL hRK hRH hht hdel ts tx hw hr z top
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
    refine writerWP_mono (hA g h v (hin v hv')) ?_
    intro _ v' hv'' hFv' key' hk'
    have := runGet_of_delInvF p ts w v' (pre ++ [cv]) (hout v' hv'' hFv').1 hI hF hFv' key' hk'
    simpa [Op.key, Op.value] using this


/-- The old case: `delStepsCaseOK_fullHG` at `DelInvI`. -/
theorem delStepsCaseOK_fullH (p : Params) (R : Struct BVal → Time → Prop) (hM : 2 ≤ p.M)
    (hsa2 : 2 ≤ p.splitAbove)
    (hRL : ∀ P t, R P t → RunLinksOK p P t)
    (hP : ∀ ts, Within p ts → PointersOK (treeRun p ts))
    (hRK : ∀ P t, R P t → KindsAllOK p P) (hRH : ∀ P t, R P t → HeightAllOK p P t)
    (hht : OpHtDelOKUnder p R) (hdel : TakeBelowFuelDelOK p)
    (hRoot : ∀ ts, DelFullRootStepOK (ctxOf p ts) (viewOf (treeRun p ts))) :
    DelStepsCaseOK p R DelFullM :=
  delStepsCaseOK_of_G p R _ (delStepsCaseOK_fullHG p R hM hsa2 hRL hP hRK hRH hht hdel hRoot _)
set_option maxHeartbeats 1600000 in
/-- The take-back of a delete into a full leaf, the merges on, from the fuel
premise after the split. -/
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
    (hRH : ∀ P t, R P t → HeightAllOK p P t) (hht : OpHtDelOKUnder p R) (hdel : TakeBelowFuelDelOK p) :
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
  obtain ⟨hvo, hkw, _, _, _, hhi, hwfw, hub⟩ := htStart_reachedU p hM R hRL hRK hRH hht hdel ts tx hw hr z top
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

end SIS.Tree
