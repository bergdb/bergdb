/-
The first stratum's delete with the merges (bergdb 025-05, step 7): one family of
case lemmas for the tree's facts (`QdW`) and the take-back's (`TakeJ2`) after a
delete, from a start with no fit and no heights' bound (`SJ0`), the obligations
entered from the tree's facts (`DelInvJT`; no reading at the leaf's change, see
Stratum.lean). It serves both stratum members that today use two families
(`DelStepsQdLJG`, `DelStepsJ2OKG`): `DelInvJT` carries `PutInv`, the ranges and
`TakeJ2` together.

The cases are those of `delMerge_cover`. The leaf with room and the full leaf are
proved here (`delInvFT_after_bitmap`, `writerWP_appendDeleteKlong_full_delT`);
the old cases keep their proofs, since they take the fit at the start and the
full leaf's root step with the fit for every context (`DelFullRootStepOK`).
-/
import SIS.Tree.Stratum

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- A delete case of the first stratum: from a start with no fit and no heights'
bound (`SJ0`) and `TakeJ2`, with the obligations over I entered from the tree's
facts (`DelInvJT`), the delete keeps `QdW` and `TakeJ2`. -/
def DelStepsCaseTJ (p : Params) (R : Struct BVal → Time → Prop) (P : Ctx → View BVal → W → Op → Prop)
    (I : List Tx → Tx → W → Key → W → Prop) : Prop :=
  ∀ ts tx, Within p (ts ++ [tx]) → R (treeRun p ts) ts.length → ∀ z top,
    lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z →
    topOf p (ctxOf p ts).view z = .ok top →
    ∀ pre op post, tx.ops = pre ++ op :: post →
    ∀ r w, (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
    SJ0 p ts tx w → TakeJ2 (ctxOf p ts) (viewOf (treeRun p ts)) tx.base w →
    ∀ key, op = .del key → P (ctxOf p ts) (viewOf (treeRun p ts)) w op →
    (∀ v, DelInvJT (ctxOf p ts) (viewOf (treeRun p ts)) (kindOracleOf p (treeRun p ts)) tx.base tx.base v →
      I ts tx w key v) →
    (∀ v, I ts tx w key v → QdW p ts v ∧ TakeJ2 (ctxOf p ts) (viewOf (treeRun p ts)) tx.base v) →
    (∀ g h v, I ts tx w key v →
      WriterWP (afterDelete key g h) (ctxOf p ts) v (fun _ v' => I ts tx w key v')) →
    (∀ g h merged v, I ts tx w key v →
      WriterWP (mergeUp key g p.fuel h merged) (ctxOf p ts) v (fun _ v' => I ts tx w key v')) →
    (∀ seg v, I ts tx w key v →
      WriterWP (collapseRoot key seg p.fuel) (ctxOf p ts) v (fun _ v' => I ts tx w key v')) →
    WriterWP (putKv op) (ctxOf p ts) w (fun _ w' =>
      QdW p ts w' ∧ TakeJ2 (ctxOf p ts) (viewOf (treeRun p ts)) tx.base w')

theorem delStepsCaseTJ_or (p : Params) (R : Struct BVal → Time → Prop)
    (P P1 P2 : Ctx → View BVal → W → Op → Prop) (I : List Tx → Tx → W → Key → W → Prop)
    (hs : ∀ c base w op, P c base w op → P1 c base w op ∨ P2 c base w op)
    (h1 : DelStepsCaseTJ p R P1 I) (h2 : DelStepsCaseTJ p R P2 I) : DelStepsCaseTJ p R P I := by
  intro ts tx hw hr z top hz htop pre op post hops r w hpre hS hJ key hop hPc hin hout hA hMU hCR
  rcases hs _ _ _ _ hPc with h | h
  · exact h1 ts tx hw hr z top hz htop pre op post hops r w hpre hS hJ key hop h hin hout hA hMU hCR
  · exact h2 ts tx hw hr z top hz htop pre op post hops r w hpre hS hJ key hop h hin hout hA hMU hCR

/-- The family from its five cases (`delMerge_cover`). -/
theorem delStepsCaseTJ_of_cases (p : Params) (R : Struct BVal → Time → Prop)
    (I : List Tx → Tx → W → Key → W → Prop)
    (c5 : DelStepsCaseTJ p R DelNoLeafM I) (c6 : DelStepsCaseTJ p R DelNoopM I)
    (c7 : DelStepsCaseTJ p R DelEmptyM I) (c8 : DelStepsCaseTJ p R DelRoomM I)
    (c9 : DelStepsCaseTJ p R DelFullM I) : DelStepsCaseTJ p R DelMergeCase I := by
  intro ts tx hw hr z top hz htop pre op post hops r w hpre hS hJ key hop hm hin hout hA hMU hCR
  obtain ⟨key', hop', hm'⟩ := hm
  rw [hop] at hop'
  cases hop'
  rcases delMerge_cover (ctxOf p ts) (viewOf (treeRun p ts)) w key hm' with h | h | h | h | h
  · exact c5 ts tx hw hr z top hz htop pre op post hops r w hpre hS hJ key hop (hop ▸ h) hin hout hA hMU hCR
  · exact c6 ts tx hw hr z top hz htop pre op post hops r w hpre hS hJ key hop (hop ▸ h) hin hout hA hMU hCR
  · exact c7 ts tx hw hr z top hz htop pre op post hops r w hpre hS hJ key hop (hop ▸ h) hin hout hA hMU hCR
  · exact c8 ts tx hw hr z top hz htop pre op post hops r w hpre hS hJ key hop (hop ▸ h) hin hout hA hMU hCR
  · exact c9 ts tx hw hr z top hz htop pre op post hops r w hpre hS hJ key hop (hop ▸ h) hin hout hA hMU hCR

/-- `QdW` and `TakeJ2` are kept by `fresh`. -/
theorem qdWJ_fresh (p : Params) (ts : List Tx) (B : NodeId) (v : W)
    (h : QdW p ts v ∧ TakeJ2 (ctxOf p ts) (viewOf (treeRun p ts)) B v) :
    WriterWP fresh (ctxOf p ts) v (fun _ v' => QdW p ts v' ∧ TakeJ2 (ctxOf p ts) (viewOf (treeRun p ts)) B v') :=
  writerWP_and (qdW_fresh p ts v h.1) (by unfold fresh; wpSimplify; exact h.2)

/-! ## The cases without a continuation -/

/-- No leaf: the state reads as before (`delStepsCaseQd_noLeafG`), and the take-back
(`writerWP_del_noLeaf_j2`). -/
theorem delStepsCaseTJ_noLeaf (p : Params) (R : Struct BVal → Time → Prop)
    (I : List Tx → Tx → W → Key → W → Prop) : DelStepsCaseTJ p R DelNoLeafM I := by
  intro ts tx hw _ _ _ _ _ ops op post hops _ w _ hS hJ _ _ hP _ _ _ _ _
  obtain ⟨key, hop, _, hno⟩ := hP
  subst hop
  have hI : PutInv (ctxOf p ts) (viewOf (treeRun p ts)) w := hS.1.1.1.1.1
  have hRO : RangeOrder (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey := hS.1.1.2
  have hkey : keyWf key = true := within_op_keyWf p ts tx hw ops _ post hops
  have hne : key ≠ [] := by intro h; subst h; simp [keyWf] at hkey
  have hno' : NoLeafFrom (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) p.fuel key
      w.top.rootKey := by
    rintro ⟨pre, cv, rk, L, n, hsplit, hrk, hvis, hn, hnl⟩
    exact hno ⟨pre, cv, L, n, hsplit, rk, hrk, hvis, hn, hnl⟩
  refine writerWP_and ?_ (writerWP_del_noLeaf_j2 (ctxOf p ts) _ (viewCoherent_ctxOf p ts) key tx.base w
    hne (hI.pathUntaken key) hno' hJ)
  unfold putKv pathClear findRoot pathAdd
  wpSimplify
  generalize hw2 : ({ ({ w with path := [] } : W) with
    path := ([] : List (Option Nat × NodeId)) ++ [(none, w.top.rootKey)] } : W) = w2
  have hr02 : ReadsAs (ctxOf p ts).p (viewOf (treeRun p ts)) w w2 := by
    subst hw2; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  refine writerWP_mono (writerWP_putSegs_del_noLeaf (ctxOf p ts) _ (viewCoherent_ctxOf p ts) key
    key w.top.rootKey w2 hne ?_ ?_) ?_
  · intro q hq
    rw [hr02.2.2.1]
    rw [hr02.1] at hq
    exact hI.pathUntaken key q hq
  · rw [hr02.1]; exact hno'
  · intro _ w' hr'
    have hr : ReadsAs p (viewOf (treeRun p ts)) w w' := ReadsAs.trans _ _ _ _ _ hr02 hr'
    refine ⟨putInv_of_readsAs _ _ w w' hI hr, ?_⟩
    rw [hr.1, hr.2.1]; exact hRO

/-- A noop: the tree, `PutInv`, the ranges and the take-back as before. -/
theorem delStepsCaseTJ_noop (p : Params) (R : Struct BVal → Time → Prop)
    (hRL : ∀ P t, R P t → RunLinksOK p P t)
    (I : List Tx → Tx → W → Key → W → Prop) : DelStepsCaseTJ p R DelNoopM I := by
  intro ts tx hw hr z top _ htop ops op _ _ r w hpre hS hJ _ _ hP _ _ _ _ _
  obtain ⟨pre, cv, L, n, hop, _, hK, hnoop⟩ := hP
  subst hop
  have hI : PutInv (ctxOf p ts) (viewOf (treeRun p ts)) w := hS.1.1.1.1.1
  have hRO : RangeOrder (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey := hS.1.1.2
  obtain ⟨rk, hrk, _⟩ := keyLeaf_rk hK
  have hB := putBase_of_run p ts tx hw (hRL _ _ hr)
  have hbook := putBook_reached p ts tx hw (hRL _ _ hr) z top htop ops r w hpre
  have hleaf := keyLeaf_all hK hrk (fun m => bitsUnion m.lastBitmap (m.bitsOf cv) = m.lastBitmap) hnoop
  refine writerWP_mono (writerWP_and (writerWP_and (writerWP_and
    (writerWP_del_noop_seg_tree (ctxOf p ts) _ (viewCoherent_ctxOf p ts) pre cv rk w hrk (hI.pathUntaken _)
      hleaf hI.tree)
    (putInv_del_noop_seg (ctxOf p ts) _ tx.base top hB pre cv rk w hI hbook hrk hleaf))
    (rangeOrder_del_noop_seg (ctxOf p ts) _ (viewCoherent_ctxOf p ts) pre cv rk w hI hRO hrk hleaf))
    (writerWP_del_noop_j2 (ctxOf p ts) _ (viewCoherent_ctxOf p ts) pre cv rk tx.base w hrk (hI.pathUntaken _)
      hleaf hJ)) ?_
  rintro _ w' ⟨⟨⟨hT, hPI⟩, hR⟩, hJ'⟩
  exact ⟨⟨hPI hT, hR⟩, hJ'⟩

/-! ## The leaf with room and the full leaf -/

set_option maxHeartbeats 1600000 in
/-- A leaf that keeps a live klong and has room: the bitmap (`delStepsCaseJ2OK_roomRG`
with the tree's facts in place of `DelInvJ`). -/
theorem delStepsCaseTJ_room (p : Params) (R : Struct BVal → Time → Prop) (hM : 2 ≤ p.M)
    (hRL : ∀ P t, R P t → RunLinksOK p P t)
    (hRP : ∀ P t, R P t → PointersOK P) (hRK : ∀ P t, R P t → KindsAllOK p P)
    (I : List Tx → Tx → W → Key → W → Prop) : DelStepsCaseTJ p R DelRoomM I := by
  intro ts tx hw hr z top _ htop ops op post hops r w hpre hS hJ key hop hPc hin hout hA _ _
  obtain ⟨pre, cv, L0, n0, hop', _, hK, hne0, hkeep0, hroom0⟩ := hPc
  subst hop'
  cases hop
  have hI : PutInv (ctxOf p ts) (viewOf (treeRun p ts)) w := hS.1.1.1.1.1
  have hRO : RangeOrder (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey := hS.1.1.2
  have hSB : tx.base ≤ w.next := hS.1.1.1.2
  have hkey : keyWf (pre ++ [cv]) = true := within_op_keyWf p ts tx hw ops _ post hops
  obtain ⟨rk, hrk, hn0⟩ := keyLeaf_rk hK
  have hB := putBase_of_run p ts tx hw (hRL _ _ hr)
  have hbook := putBook_reached p ts tx hw (hRL _ _ hr) z top htop ops r w hpre
  have hICE := innerChildren_reachedR p hM ts tx (hRP _ _ hr) (hRK _ _ hr) hw top ops (.del (pre ++ [cv]) :: post) hops r w hpre
    (fun x hx => hI.untaken x (tReach_reachS _ _ _ _ hx))
  have hLV := leafVals_all hS.1.1.1.1.2 hkey hrk
  obtain ⟨hv, hk, hb0, hi0⟩ := kd_contextR p hM ts tx (hRP _ _ hr) (hRK _ _ hr) hw top ops (.del (pre ++ [cv]) :: post) hops r w hpre
  have hJ0 : KdJ (ctxOf p ts) tx.base top (kindOracleOf p (treeRun p ts)) tx.base w := ⟨hbook, hb0, hi0⟩
  refine writerWP_del_toLeafMK (ctxOf p ts) _ (viewCoherent_ctxOf p ts) pre cv rk w _ hJ0
    (fun s f x v hJ hx => kdJ_descendLte _ _ tx.base top hB _ tx.base hv hk s f x v hJ hx)
    (fun s x L n v hJ hL hlk hkm => kdJ_pathAdd _ _ tx.base top hB _ tx.base hv s x L n v hJ hL hlk hkm)
    (kdJ_start _ _ tx.base top hB _ tx.base hv w hJ0) hrk (hI.pathUntaken _) hI.wf _
    (fun v hv' => qdWJ_fresh p ts tx.base v hv') ?_
  intro L n P w3 hL hn hnl hr03 hJ3 hlk3 hp3' _ hXD _
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
    (fun v => DelInvJT (ctxOf p ts) (viewOf (treeRun p ts)) (kindOracleOf p (treeRun p ts)) tx.base tx.base v)
    _ ?_ ?_
  · refine writerWP_mono (writerWP_and (writerWP_and
      (writerWP_appendDeleteKlong_room_exactD L _ cv n _ _ hlk3 htimes hwf hne hroomD)
      (putBook_appendDeleteKlong L _ cv _ _ tx.base top hB _ hJ3.1))
      (kd_appendDeleteKlong _ tx.base L P.length cv _ w3 hv hk hJ3.2.1 hJ3.2.2 a hpx)) ?_
    rintro _ v ⟨⟨⟨h1, h2, h3, _, h5, _, h7⟩, hbv⟩, hkv⟩
    obtain ⟨a1, a2, a3, a4⟩ := delInvFT_after_bitmap (ctxOf p ts) _ tx.base top hB w w3 v cv L n hI hRO hICE
      hn hnl hr03 hLt h1 h2 h3 h7 hbv
    refine ⟨⟨a1, a2, a3, a4, ⟨tx.base, top, hB, hbv⟩, hkv.1, hkv.2.1⟩, ?_, ?_⟩
    · exact takeJ2_after_bitmap (ctxOf p ts) _ tx.base w3 v cv L n (by simp [ctxOf]) hJ23 hlk3
        (by rw [hr03.2.2.1]; exact hLt) (hI.times L n hn)
        (by rw [hr03.1, hr03.2.1]; exact keyLeaf_reached hI hrk L hL)
        (fun y hy => by rw [hr03.1]; exact (hLV L n hL hn hnl y hy).1)
        (fun y hy => by rw [hr03.2.2.2.1]; exact (hLV L n hL hn hnl y hy).2) h1 h2 h3 h7
    · rw [h5, hr03.2.2.2.2]; exact hSB
  · intro g h v hv'
    exact writerWP_mono (hA g h v (hin v hv')) (fun _ v' hv'' => hout v' hv'')

set_option maxHeartbeats 1600000 in
/-- A full leaf: the bitmap's split (`delStepsCaseJ2OK_fullSG` with the tree's facts
in place of `DelInvJ`, the walk with the kinds' books only). -/
theorem delStepsCaseTJ_full (p : Params) (R : Struct BVal → Time → Prop) (hM : 2 ≤ p.M)
    (hsa2 : 2 ≤ p.splitAbove)
    (hRL : ∀ P t, R P t → RunLinksOK p P t)
    (hRP : ∀ P t, R P t → PointersOK P) (hRK : ∀ P t, R P t → KindsAllOK p P)
    (I : List Tx → Tx → W → Key → W → Prop) : DelStepsCaseTJ p R DelFullM I := by
  intro ts tx hw hr z top _ htop ops op post hops r w hpre hS hJ key hop hPc hin hout hA _ _
  obtain ⟨pre, cv, L0, n0, hop', _, hK, hne0, hkeep0, hfull0⟩ := hPc
  subst hop'
  cases hop
  have hI : PutInv (ctxOf p ts) (viewOf (treeRun p ts)) w := hS.1.1.1.1.1
  have hRO : RangeOrder (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey := hS.1.1.2
  have hSB : tx.base ≤ w.next := hS.1.1.1.2
  have hkey : keyWf (pre ++ [cv]) = true := within_op_keyWf p ts tx hw ops _ post hops
  obtain ⟨rk, hrk, _⟩ := keyLeaf_rk hK
  have hB := putBase_of_run p ts tx hw (hRL _ _ hr)
  have hbook := putBook_reached p ts tx hw (hRL _ _ hr) z top htop ops r w hpre
  have hG := putInvG_of_book _ _ tx.base top w hB hbook
  have hLV := leafVals_all hS.1.1.1.1.2 hkey hrk
  have hpos : 0 < (ctxOf p ts).i := by simp [ctxOf]
  obtain ⟨hv, hk, hb0, hi0⟩ := kd_contextR p hM ts tx (hRP _ _ hr) (hRK _ _ hr) hw top ops (.del (pre ++ [cv]) :: post) hops r w hpre
  have hKall := hRK _ _ hr
  have hICEk : ICEFromKinds (ctxOf p ts) (viewOf (treeRun p ts)) (kindOracleOf p (treeRun p ts)) tx.base :=
    fun v hb hi hun => innerChildren_of_kinds p (treeRun p ts) tx.base (ctxOf p ts) v rfl hKall
      (hRP _ _ hr) hb hi.cache hun
  have hJ0 : KdJ (ctxOf p ts) tx.base top (kindOracleOf p (treeRun p ts)) tx.base w := ⟨hbook, hb0, hi0⟩
  refine writerWP_del_toLeafMK (ctxOf p ts) _ (viewCoherent_ctxOf p ts) pre cv rk w _ hJ0
    (fun s f x v hJ hx => kdJ_descendLte _ _ tx.base top hB _ tx.base hv hk s f x v hJ hx)
    (fun s x L n v hJ hL hlk hkm => kdJ_pathAdd _ _ tx.base top hB _ tx.base hv s x L n v hJ hL hlk hkm)
    (kdJ_start _ _ tx.base top hB _ tx.base hv w hJ0) hrk (hI.pathUntaken _) hI.wf _
    (fun v hv' => qdWJ_fresh p ts tx.base v hv') ?_
  intro L n P w3 hL hn hnl hr03 hJ3 hlk3 hp3' hlinkP hXD hlkX
  obtain ⟨hne, hkeep, hfull⟩ := keyLeaf_all2 hK hrk
    (fun _ m => bitsUnion m.lastBitmap (m.bitsOf cv) ≠ m.lastBitmap ∧
      m.allKeysIn (bitsUnion m.lastBitmap (m.bitsOf cv)) = false ∧ ¬ DelRoom (ctxOf p ts) cv m)
    ⟨hne0, hkeep0, hfull0⟩ L n hL hn hnl
  have hPOK := pathOK_of_toLeaf (ctxOf p ts) _ w w3 P n hI hr03 hp3' hlinkP hlkX
  have hJ3' : TakeJ2 (ctxOf p ts) (viewOf (treeRun p ts)) tx.base w3 := takeJ2_of_readsAs _ _ _ w w3 hJ hr03
  have hJ2 := writerWP_appendDeleteKlong_full_j2_any (ctxOf p ts) _ tx.base hpos
    (delFullRootJ2OK_ctx p hsa2 ts tx.base) w3
    (putInv_of_readsAs _ _ w w3 hI hr03) (putInvG_of_readsAs _ _ w w3 hG hr03)
    (by rw [hr03.1, hr03.2.1]; exact hRO) hJ3' (by rw [hr03.2.2.2.2]; exact hSB) hsa2
    P.length _ _ _ hPOK cv n (by show (wNode _ _ w (nodeAt w.top.rootKey P P.length)).getD _ = n; rw [hXD, hn]; rfl)
    hnl hne hfull (fun y hy => by rw [hr03.1]; exact (hLV L n hL hn hnl y hy).1)
  simp only [hXD] at hJ2
  refine writerWP_deleteUpward_full (ctxOf p ts) L n P.length cv (pre ++ [cv]) w3 hlk3 hne hkeep
    (fun v => DelInvJT (ctxOf p ts) (viewOf (treeRun p ts)) (kindOracleOf p (treeRun p ts)) tx.base tx.base v)
    _ (writerWP_mono (writerWP_and (writerWP_appendDeleteKlong_full_delT (ctxOf p ts) _ (viewCoherent_ctxOf p ts)
      _ tx.base (delFullRootStepOKT_ctx p ts) hsa2 hv hk hICEk w pre cv rk tx.base top hB hI hRO
      hkey hrk L n P w3 hL hn hnl hne hfull hr03 hJ3 hp3' hlinkP hXD hlkX) hJ2)
      (fun _ v hv' => ⟨hv'.1, hv'.2.1, hv'.2.2⟩)) ?_
  intro g h v hv'
  exact writerWP_mono (hA g h v (hin v hv')) (fun _ v' hv'' => hout v' hv'')

/-! ## The leaf emptied: room above, the space root -/

set_option maxHeartbeats 1600000 in
/-- `writerWP_del_emptyRoomMJKG` in the first stratum (bergdb 025-05, step 7): no fit at
the start, the continuations given the tree's facts (`DelInvJT`); the upward walk with
the fit at the next id's depth (P1, `takeJ2_deleteUpward_upTMBKD`). -/
theorem writerWP_del_emptyRoomMJKT (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (pre : List Nat) (cv : Nat) (rk : NodeId) (w : W) (B : NodeId) (top0 : Top)
    (hB : PutBase c base B) (hbook : PutBook c B top0 w)
    (KO : KindOracle) (BK : NodeId) (hvB : ViewIdsBelow BK c.view) (hk : ViewKinds KO BK c)
    (hb0 : Book BK c w) (hi0 : KdInv KO BK w)
    (hI : PutInv c base w) (hRO : RangeOrder (wNode c.p base w) c.i w.top.rootKey)
    (hICE : InnerChildrenExist (wNode c.p base w) c.i w.top.rootKey)
    (hkey : keyWf (pre ++ [cv]) = true)
    (hrk : segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk)
    (hleafC : ∀ L n, (L, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      wNode c.p base w L = some n → n.leaf = true →
      bitsUnion n.lastBitmap (n.bitsOf cv) ≠ n.lastBitmap ∧
      n.allKeysIn (bitsUnion n.lastBitmap (n.bitsOf cv)) = true ∧ UpRoom c base w L n)
    (hm : c.p.merges = true) (hpos : 0 < c.i)
    (hJ2 : TakeJ2 c base B w) (hMF : ∀ x o, w.madeFor.lookup x = some o → o < B)
    (hLV : ∀ L n, (L, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      wNode c.p base w L = some n → n.leaf = true → ∀ y, (cv, y) ∈ n.liveAt c.i →
      wNode c.p base w y = none)
    (Post : W → Prop) (hfresh : ∀ v, Post v → WriterWP fresh c v (fun _ v' => Post v'))
    (Imid : W → Prop)
    (hA : ∀ g h v, DelInvJT c base KO BK B v →
      WriterWP (afterDelete (pre ++ [cv]) g h) c v (fun _ v' => Post v'))
    (hMU : ∀ g h merged v, DelInvJT c base KO BK B v →
      WriterWP (mergeUp (pre ++ [cv]) g c.p.fuel h merged) c v (fun _ v' => Imid v'))
    (hCR : ∀ seg v, Imid v →
      WriterWP (collapseRoot (pre ++ [cv]) seg c.p.fuel) c v (fun _ v' => Post v')) :
    WriterWP (putKv (.del (pre ++ [cv]))) c w (fun _ w' => Post w') := by
  have hfuel : 1 ≤ c.p.fuel := by unfold Params.fuel; omega
  refine writerWP_del_toLeafMK c base hvc pre cv rk w (fun v => KdJ c B top0 KO BK v ∧ v.madeFor = w.madeFor)
    ⟨⟨hbook, hb0, hi0⟩, rfl⟩
    (fun s f x v hJ hx => writerWP_mono (writerWP_and (kdJ_descendLte c base B top0 hB KO BK hvB hk s f x v hJ.1 hx)
      (writerWP_descendLte_madeFor s c f x v)) (fun _ v' h => ⟨h.1, h.2.trans hJ.2⟩))
    (fun s x L n v hJ hL hlk hkm => ⟨kdJ_pathAdd c base B top0 hB KO BK hvB s x L n v hJ.1 hL hlk hkm, hJ.2⟩)
    ⟨kdJ_start c base B top0 hB KO BK hvB w ⟨hbook, hb0, hi0⟩, rfl⟩ hrk (hI.pathUntaken _) hI.wf
    Post hfresh ?_
  intro L n P w3 hL hn hnl hr03 hJ3 hlk3 hp3' hlinkP hXD hlkX
  have hb3 := hJ3.1
  have hMF3 : ∀ x o, w3.madeFor.lookup x = some o → o < B := by rw [hJ3.2]; exact hMF
  have hJ23 : TakeJ2 c base B w3 := takeJ2_of_readsAs c base B w w3 hJ2 hr03
  obtain ⟨hne, hall, hup⟩ := hleafC L n hL hn hnl
  obtain ⟨hdepth, hstopOK⟩ := hup P hlinkP hXD
  -- the path, at w
  have hgetP := LinkedFrom.get _ _ _ P hlinkP
  have hXN : ∀ i, i ≤ P.length → wNode c.p base w (nodeAt w.top.rootKey P i) =
      some ((wNode c.p base w (nodeAt w.top.rootKey P i)).getD n) := by
    intro i hi
    rcases Nat.lt_or_ge i P.length with hlt | hge
    · obtain ⟨_, n', _, h2, _⟩ := hgetP i hlt
      rw [h2]; rfl
    · have : i = P.length := by omega
      subst this
      rw [hXD, hn]; rfl
  have hKP : ∀ i, 0 < i → i ≤ P.length →
      P[i - 1]? = some (some (((P[i - 1]?).bind (·.1)).getD 0), nodeAt w.top.rootKey P i) ∧
      (((P[i - 1]?).bind (·.1)).getD 0, nodeAt w.top.rootKey P i) ∈
        ((wNode c.p base w (nodeAt w.top.rootKey P (i - 1))).getD n).liveAt c.i := by
    intro i h1 h2
    obtain ⟨k, n', e1, e2, e3⟩ := hgetP (i - 1) (by omega)
    have hi : i - 1 + 1 = i := by omega
    rw [hi] at e1 e3
    rw [e1, e2]
    exact ⟨rfl, e3⟩
  have hPL := LinkedFrom.pathLen _ _ _ P hlinkP
  have hreachX : ∀ i, i ≤ P.length →
      TReach (wNode c.p base w) c.i w.top.rootKey (nodeAt w.top.rootKey P i) :=
    fun i hi => (hPL i hi).reach
  have hdistP : ∀ i i', i ≤ P.length → i' ≤ P.length →
      nodeAt w.top.rootKey P i = nodeAt w.top.rootKey P i' → i = i' := by
    intro i i' h1 h2 he
    have a := hPL i h1
    have b := hPL i' h2
    rw [he] at a
    exact PathLen.depth_unique hI.tree _ _ _ a b
  have hpX : ∀ i, i ≤ P.length → (w3.path[i]?).map (·.2) = some (nodeAt w.top.rootKey P i) := by
    intro i hi
    have hl : i < (w.top.rootKey :: P.map (·.2)).length := by simp; omega
    rw [hp3', ← List.getElem?_map, List.map_cons, List.getElem?_eq_getElem hl]
    simp [nodeAt, List.getElem?_eq_getElem hl]
  have hpK : ∀ i, 0 < i → i ≤ P.length →
      w3.path[i]? = some (some (((P[i - 1]?).bind (·.1)).getD 0), nodeAt w.top.rootKey P i) := by
    intro i h1 h2
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    rw [hp3', List.getElem?_cons_succ]
    exact (hKP (j + 1) h1 h2).1
  -- the facts at w3
  have hN3 : ∀ i, i ≤ P.length → wNode c.p base w3 (nodeAt w.top.rootKey P i) =
      some ((wNode c.p base w (nodeAt w.top.rootKey P i)).getD n) := fun i hi => by
    rw [hr03.1]; exact hXN i hi
  have htk3 : ∀ i, i ≤ P.length → w3.taken.contains (nodeAt w.top.rootKey P i) = false := fun i hi => by
    rw [hr03.2.2.1]; exact hI.untaken _ (tReach_reachS _ _ _ _ (hreachX i hi))
  have hT3 : TreeOK (wNode c.p base w3) c.i w3.top.rootKey := by rw [hr03.1, hr03.2.1]; exact hI.tree
  have hR3 : RangeOrder (wNode c.p base w3) c.i w3.top.rootKey := by rw [hr03.1, hr03.2.1]; exact hRO
  have hwf3 : ∀ x xn, TReach (wNode c.p base w3) c.i w3.top.rootKey x → wNode c.p base w3 x = some xn →
      klongsWf xn.ks = true := fun x xn _ h => by rw [hr03.1] at h; exact hI.wf x xn h
  have hRt3 : ∀ y, TReach (wNode c.p base w3) c.i w3.top.rootKey y → w3.taken.contains y = false := by
    intro y hy
    rw [hr03.1, hr03.2.1] at hy
    rw [hr03.2.2.1]
    exact hI.untaken y (tReach_reachS _ _ _ _ hy)
  have hTimesR3 : ∀ y yn, TReach (wNode c.p base w3) c.i w3.top.rootKey y → wNode c.p base w3 y = some yn →
      ∀ s, Klong.time s ∈ yn.ks → s ≤ c.i := fun y yn _ h => by rw [hr03.1] at h; exact hI.times y yn h
  have hICE3 : InnerChildrenExist (wNode c.p base w3) c.i w3.top.rootKey := by
    rw [hr03.1, hr03.2.1]; exact hICE
  have hfit3 : SegFits (wNode c.p base w3) c.i w3.next w3.top.rootKey :=
    segFits_next_of_putInv c base w3 (putInv_of_readsAs c base w w3 hI hr03)
  have hnovalAll3 : ∀ y yn, wNode c.p base w3 y = some yn → wValue base w3 y = none := by
    intro y yn h
    rw [hr03.1] at h
    rw [ReadsAs.value _ _ _ _ hr03]
    exact hI.keyNoValue y yn h
  have hreach3 : ∀ i, i ≤ P.length →
      TReach (wNode c.p base w3) c.i w3.top.rootKey (nodeAt w.top.rootKey P i) := fun i hi => by
    rw [hr03.1, hr03.2.1]; exact hreachX i hi
  have hlinkK : ∀ i, 0 < i → i ≤ P.length →
      (((P[i - 1]?).bind (·.1)).getD 0, nodeAt w.top.rootKey P i) ∈
        ((wNode c.p base w (nodeAt w.top.rootKey P (i - 1))).getD n).liveAt c.i :=
    fun i h1 h2 => (hKP i h1 h2).2
  have hNnD : (wNode c.p base w (nodeAt w.top.rootKey P P.length)).getD n = n := by rw [hXD, hn]; rfl
  -- the tree's facts at a continuation of the upward delete
  have hD : ∀ (stop : Nat) (w' : W) (sn' : KNode) (f : Nat → Nat), stop < P.length →
      (∀ y, (∀ k, stop < k → k ≤ P.length → y ≠ nodeAt w.top.rootKey P k) →
        w'.taken.contains y = w3.taken.contains y) →
      w'.top = w3.top → w'.vals = w3.vals →
      (∀ y, y ≠ nodeAt w.top.rootKey P stop → (∀ k, stop < k → k ≤ P.length → y ≠ nodeAt w.top.rootKey P k) →
        w'.nodes.lookup y = w3.nodes.lookup y) →
      w'.nodes.lookup (nodeAt w.top.rootKey P stop) = some sn' →
      sn'.leaf = ((wNode c.p base w (nodeAt w.top.rootKey P stop)).getD n).leaf →
      klongsWf sn'.ks = true → (∀ s, Klong.time s ∈ sn'.ks → s ≤ c.i) →
      (∀ c' z, (c', z) ∈ sn'.liveAt c.i →
        ∃ c0, (c0, z) ∈ ((wNode c.p base w (nodeAt w.top.rootKey P stop)).getD n).liveAt c.i ∧
          c0 ≠ ((P[stop + 1 - 1]?).bind (·.1)).getD 0 ∧ f c0 = c') →
      RangeOrder (wNode c.p base w') c.i w'.top.rootKey →
      PutBook c B top0 w' → Book BK c w' → KdInv KO BK w' →
      DelInvT c base KO BK w' := by
    intro stop w' sn' f hsD ht htop hv hnodes hsn' hsl' hsw' hst' hlive' hRO' hb' hbk hik
    have hCG := collGetInvD_after_upT c base (fun i => nodeAt w.top.rootKey P i)
      (fun i => (wNode c.p base w (nodeAt w.top.rootKey P i)).getD n)
      (fun i => ((P[i - 1]?).bind (·.1)).getD 0) P.length w3 hlkX htk3 hdistP hT3 hwf3 hRt3 hTimesR3
      hICE3 w3.next hfit3 hnovalAll3 hreach3 hlinkK stop w' sn' f hsD ht htop hv hnodes hsn' hsl' hsw' hst' hlive'
    have hG := putInvG_of_book c base B top0 w' hB hb'
    have hPI : PutInv c base w' := putInv_of_parts c base w' hG hCG.1.1
      (fun y hy => hCG.1.2.1 y (reachS_tReach _ _ _ _ hy))
      (leafOrder_of_rangeOrder _ _ _ hRO' hG.times)
    exact ⟨hPI, hG, hRO', fun y yn cc z hy hyn hl hz => hCG.1.2.2.2 y yn cc z hy hyn hl hz,
      ⟨B, top0, hB, hb'⟩, hbk, hik⟩
  -- the frame facts at a continuation
  have hXs : ∀ stop, stop < P.length → ∀ k, stop < k → k ≤ P.length →
      nodeAt w.top.rootKey P stop ≠ nodeAt w.top.rootKey P k :=
    fun stop _ k h1 h2 he => by have := hdistP _ _ (by omega) h2 he; omega
  have hfr : ∀ (stop : Nat) (w' : W) (sn' : KNode), stop < P.length →
      (∀ y, (∀ k, stop < k → k ≤ P.length → y ≠ nodeAt w.top.rootKey P k) →
        w'.taken.contains y = w3.taken.contains y) →
      (∀ y, y ≠ nodeAt w.top.rootKey P stop → (∀ k, stop < k → k ≤ P.length → y ≠ nodeAt w.top.rootKey P k) →
        w'.nodes.lookup y = w3.nodes.lookup y) →
      w'.nodes.lookup (nodeAt w.top.rootKey P stop) = some sn' →
      (∀ u, u ≠ nodeAt w.top.rootKey P stop → (∀ i, stop < i → i ≤ P.length → u ≠ nodeAt w.top.rootKey P i) →
        wNode c.p base w' u = wNode c.p base w3 u) ∧
      wNode c.p base w' (nodeAt w.top.rootKey P stop) = some sn' := by
    intro stop w' sn' hsD ht hnodes hsn'
    refine ⟨fun u hus hnc => by simp only [wNode, ht u hnc, hnodes u hus hnc], ?_⟩
    simp only [wNode, ht _ (hXs stop hsD), htk3 stop (by omega), Bool.false_eq_true, ↓reduceIte, hsn']
  rw [← hXD]
  have hcvAll : ∀ c' z, (c', z) ∈ n.liveAt c.i → c' = cv := by
    intro c' z hm'
    have hnt := hI.times L n hn
    have hm2 : (c', z) ∈ n.live := by rw [← KNode.liveAt_of_times _ c.i hnt]; exact hm'
    exact allKeysIn_live_cv n cv hall c' z hm2
  refine takeJ2_deleteUpward_upTMBKD c base (fun i => nodeAt w.top.rootKey P i)
    (fun i => (wNode c.p base w (nodeAt w.top.rootKey P i)).getD n)
    (fun i => ((P[i - 1]?).bind (·.1)).getD 0) P.length cv pre rk B w3 hdepth hfuel hpos hpX hpK hlkX htk3
    (fun i hi => hTimesR3 _ _ (hreach3 i hi) (hN3 i hi))
    hdistP (by rw [hNnD]; exact hne) (by rw [hNnD]; exact hall) (by rw [hNnD]; exact hnl) hT3 hR3 hwf3 hRt3
    hTimesR3 hICE3 w3.next hfit3 hnovalAll3 hreach3
    hlinkK (by rw [hr03.1, hr03.2.1]; exact hrk)
    (keyWf_last_notin pre cv hkey) (by rw [hr03.1, hXD]; exact hL)
    (by rw [hr03.1, hr03.2.1]; exact hI.keyUniq pre cv rk hkey hrk) hstopOK hm
    (fun c' z hz => by
      rw [hNnD] at hz
      have := hcvAll c' z hz
      subst this
      rw [hr03.1]; exact hLV L n hL hn hnl z hz) hJ23 hMF3 _
    (KdJP c B top0 KO BK w3.path) ⟨hb3, rfl⟩ (fun s v hJ => kdJP_note c base B top0 hB KO BK hvB hk _ s v hJ)
    (fun x q k v hJ hx => kdJP_takeBack c base B top0 hB KO BK hvB hk _ x q k v hJ hx)
    (fun x v hJ => kdJP_unlink c base B top0 hB KO BK hvB hk _ x v hJ)
    (fun x d k v hJ hx => kdJP_appendDeleteKlong c base B top0 hB KO BK hvB hk _ x d k v hJ hx)
    (fun x d v xn hJ hx hl hxl => kdJP_emptyKeyNext c base B top0 hB KO BK hvB hk _ x d v xn hJ hx hl hxl) ?_ ?_ ?_
  · intro seg stop w' sn' hsD hbetween ht htop hv hnodes hsn' hsl' hsw' hst' hlive' _ _ _ _ hJv _ hb' gs hs
    obtain ⟨hagree, hsnw⟩ := hfr stop w' sn' hsD ht hnodes hsn'
    have hRO' : RangeOrder (wNode c.p base w') c.i w'.top.rootKey := by
      rw [htop]
      exact rangeOrder_up_bitmap (wNode c.p base w3) (wNode c.p base w') c.i w3.top.rootKey _ _ _ stop
        P.length hsD hR3 hT3 (hreach3 stop (by omega)) (fun i _ h2 => hN3 i h2)
        (fun i h1 h2 => hlinkK i (by omega) h2) (fun i i' _ h2 _ h4 he => hdistP i i' h2 h4 he)
        hagree sn' hsnw hsl' (fun c' z h => (hlive' c' z).mp h)
    have hDv := hD stop w' sn' id hsD ht htop hv hnodes hsn' hsl' hsw' hst'
      (fun c' z h => ⟨c', ((hlive' c' z).mp h).1, ((hlive' c' z).mp h).2, rfl⟩) hRO' hb'.1.1 hb'.1.2.1 hb'.1.2.2
    refine writerWP_mono (hMU gs hs false w' ⟨hDv, hJv, hb'.1.1.fresh.1⟩) ?_
    intro _ w1 hD1
    exact hCR seg w1 hD1
  · intro stop w' sn' hsD hbetween ht htop hv hnodes hsn' hsl' hsw' hst' hlive' _ _ _ _ hJv _ hb' gs hs
    obtain ⟨hagree, hsnw⟩ := hfr stop w' sn' hsD ht hnodes hsn'
    have hRO' : RangeOrder (wNode c.p base w') c.i w'.top.rootKey := by
      rw [htop]
      exact rangeOrder_up_bitmap (wNode c.p base w3) (wNode c.p base w') c.i w3.top.rootKey _ _ _ stop
        P.length hsD hR3 hT3 (hreach3 stop (by omega)) (fun i _ h2 => hN3 i h2)
        (fun i h1 h2 => hlinkK i (by omega) h2) (fun i i' _ h2 _ h4 he => hdistP i i' h2 h4 he)
        hagree sn' hsnw hsl' (fun c' z h => (hlive' c' z).mp h)
    have hDv := hD stop w' sn' id hsD ht htop hv hnodes hsn' hsl' hsw' hst'
      (fun c' z h => ⟨c', ((hlive' c' z).mp h).1, ((hlive' c' z).mp h).2, rfl⟩) hRO' hb'.1.1 hb'.1.2.1 hb'.1.2.2
    exact hA gs hs w' ⟨hDv, hJv, hb'.1.1.fresh.1⟩
  · intro seg stop w' sn' jcv jy hsD hbetween ht htop hv hnodes hsn' hsl' hsw' hst' hsl hK0 hj hj0 hmin
      hlive' _ _ _ _ hJv _ hb' gs hs
    obtain ⟨hagree, hsnw⟩ := hfr stop w' sn' hsD ht hnodes hsn'
    have hRO' : RangeOrder (wNode c.p base w') c.i w'.top.rootKey := by
      rw [htop]
      exact rangeOrder_up_leb (wNode c.p base w3) (wNode c.p base w') c.i w3.top.rootKey _ _ _ stop
        P.length hsD hR3 hT3 (hreach3 stop (by omega)) (fun i _ h2 => hN3 i h2)
        (fun i h1 h2 => hlinkK i (by omega) h2) (fun i i' _ h2 _ h4 he => hdistP i i' h2 h4 he)
        hagree sn' hsnw hsl hsl' hK0 jcv jy hj hj0 hmin hlive'
    have hDv := hD stop w' sn' (fun c' => if c' = jcv then 0 else c') hsD ht htop hv hnodes hsn' hsl' hsw' hst'
      (by
        intro c' z h
        rcases (hlive' c' z).mp h with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
        · refine ⟨jcv, by rw [h2]; exact hj, by omega, ?_⟩
          simp [h1]
        · exact ⟨c', h1, by omega, by simp [h3]⟩) hRO' hb'.1.1 hb'.1.2.1 hb'.1.2.2
    refine writerWP_mono (hMU gs hs false w' ⟨hDv, hJv, hb'.1.1.fresh.1⟩) ?_
    intro _ w1 hD1
    exact hCR seg w1 hD1


set_option maxHeartbeats 1600000 in
/-- The upward delete with room above the leaf (`delStepsCaseJ2OK_emptyRoomRG` over the
stratum's walk `writerWP_del_emptyRoomMJKT`). -/
theorem delStepsCaseTJ_emptyRoom (p : Params) (R : Struct BVal → Time → Prop) (hM : 2 ≤ p.M)
    (hRL : ∀ P t, R P t → RunLinksOK p P t)
    (hRP : ∀ P t, R P t → PointersOK P) (hRK : ∀ P t, R P t → KindsAllOK p P)
    (I : List Tx → Tx → W → Key → W → Prop) : DelStepsCaseTJ p R DelEmptyRoomM I := by
  intro ts tx hw hr z top _ htop ops op post hops r w hpre hS hJ key hop hPc hin hout hA hMU hCR
  obtain ⟨pre, cv, L0, n0, hop', hm, hK, hne0, hall0, hup0⟩ := hPc
  subst hop'
  cases hop
  have hI : PutInv (ctxOf p ts) (viewOf (treeRun p ts)) w := hS.1.1.1.1.1
  have hRO : RangeOrder (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey := hS.1.1.2
  have hkey : keyWf (pre ++ [cv]) = true := within_op_keyWf p ts tx hw ops _ post hops
  obtain ⟨rk, hrk, _⟩ := keyLeaf_rk hK
  have hB := putBase_of_run p ts tx hw (hRL _ _ hr)
  have hbook := putBook_reached p ts tx hw (hRL _ _ hr) z top htop ops r w hpre
  have hICE := innerChildren_reachedR p hM ts tx (hRP _ _ hr) (hRK _ _ hr) hw top ops (.del (pre ++ [cv]) :: post) hops r w hpre
    (fun x hx => hI.untaken x (tReach_reachS _ _ _ _ hx))
  have hLV := leafVals_all hS.1.1.1.1.2 hkey hrk
  obtain ⟨hv, hk, hb0, hi0⟩ := kd_contextR p hM ts tx (hRP _ _ hr) (hRK _ _ hr) hw top ops (.del (pre ++ [cv]) :: post) hops r w hpre
  exact writerWP_del_emptyRoomMJKT (ctxOf p ts) _ (viewCoherent_ctxOf p ts) pre cv rk w tx.base top hB hbook
    _ tx.base hv hk hb0 hi0 hI hRO hICE hkey hrk (keyLeaf_all2 hK hrk _ ⟨hne0, hall0, hup0⟩) hm
    (by simp [ctxOf]) hJ hS.1.2 (fun L n hL hn hnl y hy => (hLV L n hL hn hnl y hy).1) _
    (fun v hv' => qdWJ_fresh p ts tx.base v hv') _
    (fun g h v hv => writerWP_mono (hA g h v (hin v hv)) (fun _ v' hv' => hout v' hv')) (fun g h m v
      hv => hMU g h m v (hin v hv)) (fun seg v hv => writerWP_mono (hCR seg v hv) (fun _ v' hv' =>
      hout v' hv'))

set_option maxHeartbeats 1600000 in
/-- The leaf at the space root emptied: the root's bitmap, or its split when full; no
merges' loop (`delStepsCaseQd_emptyRootG` and `delStepsCaseJ2OK_emptyRootRG` with the
tree-facts forms of the leaf's change). -/
theorem delStepsCaseTJ_emptyRoot (p : Params) (R : Struct BVal → Time → Prop) (hM : 2 ≤ p.M)
    (hsa2 : 2 ≤ p.splitAbove)
    (hRL : ∀ P t, R P t → RunLinksOK p P t)
    (hRP : ∀ P t, R P t → PointersOK P) (hRK : ∀ P t, R P t → KindsAllOK p P)
    (I : List Tx → Tx → W → Key → W → Prop) : DelStepsCaseTJ p R DelEmptyRootM I := by
  intro ts tx hw hr z top _ htop ops op post hops r w hpre hS hJ key hop hPc _ _ _ _ _
  obtain ⟨pre, cv, L0, n0, hop', _, hK, hne0, hall0, hroot0⟩ := hPc
  subst hop'
  cases hop
  have hI : PutInv (ctxOf p ts) (viewOf (treeRun p ts)) w := hS.1.1.1.1.1
  have hRO : RangeOrder (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey := hS.1.1.2
  have hSB : tx.base ≤ w.next := hS.1.1.1.2
  have hkey : keyWf (pre ++ [cv]) = true := within_op_keyWf p ts tx hw ops _ post hops
  obtain ⟨rk, hrk, _⟩ := keyLeaf_rk hK
  have hB := putBase_of_run p ts tx hw (hRL _ _ hr)
  have hbook := putBook_reached p ts tx hw (hRL _ _ hr) z top htop ops r w hpre
  have hG := putInvG_of_book _ _ tx.base top w hB hbook
  have hICE := innerChildren_reachedR p hM ts tx (hRP _ _ hr) (hRK _ _ hr) hw top ops (.del (pre ++ [cv]) :: post) hops r w hpre
    (fun x hx => hI.untaken x (tReach_reachS _ _ _ _ hx))
  have hLV := leafVals_all hS.1.1.1.1.2 hkey hrk
  have hpos : 0 < (ctxOf p ts).i := by simp [ctxOf]
  obtain ⟨hv, hk, hb0, hi0⟩ := kd_contextR p hM ts tx (hRP _ _ hr) (hRK _ _ hr) hw top ops (.del (pre ++ [cv]) :: post) hops r w hpre
  have hJ0 : KdJ (ctxOf p ts) tx.base top (kindOracleOf p (treeRun p ts)) tx.base w := ⟨hbook, hb0, hi0⟩
  refine writerWP_del_toLeafMK (ctxOf p ts) _ (viewCoherent_ctxOf p ts) pre cv rk w _ hJ0
    (fun s f x v hJ hx => kdJ_descendLte _ _ tx.base top hB _ tx.base hv hk s f x v hJ hx)
    (fun s x L n v hJ hL hlk hkm => kdJ_pathAdd _ _ tx.base top hB _ tx.base hv s x L n v hJ hL hlk hkm)
    (kdJ_start _ _ tx.base top hB _ tx.base hv w hJ0) hrk (hI.pathUntaken _) hI.wf _
    (fun v hv' => qdWJ_fresh p ts tx.base v hv') ?_
  intro L n P w3 hL hn hnl hr03 hJ3 hlk3 hp3' hlinkP hXD hlkX
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
  have hb3' := putBook_note "up.root-kept-empty" (ctxOf p ts) _ tx.base top hB w3 hJ3.1
  have hJ3' : TakeJ2 (ctxOf p ts) (viewOf (treeRun p ts)) tx.base
      ({ w3 with trail := "up.root-kept-empty" :: w3.trail } : W) := takeJ2_of_readsAs _ _ _ w _ hJ hr03'
  have hLt : w.taken.contains L = false :=
    hI.pathUntaken _ (L, cv) (fromVisits_append _ _ _ pre cv _ rk hrk _ hL)
  have hcvN : ∀ y, (cv, y) ∈ n.liveAt (ctxOf p ts).i →
      wNode (ctxOf p ts).p (viewOf (treeRun p ts)) ({ w3 with trail := "up.root-kept-empty" :: w3.trail } : W) y
        = none := fun y hy => by rw [hr03'.1]; exact (hLV L n hL hn hnl y hy).1
  by_cases hroom : DelRoom (ctxOf p ts) cv n
  · refine writerWP_mono (writerWP_and
      (writerWP_appendDeleteKlong_room_exactD L _ cv n _ _ hlk3 (hI.times L n hn) (hI.wf L n hn) hne hroom)
      (putBook_appendDeleteKlong L _ cv _ _ tx.base top hB _ hb3')) ?_
    rintro _ v ⟨⟨h1, h2, h3, _, _, _, h7⟩, hbv⟩
    have hD := delInvFT_after_bitmap (ctxOf p ts) _ tx.base top hB w _ v cv L n hI hRO hICE
      hn hnl hr03' hLt h1 h2 h3 h7 hbv
    refine ⟨⟨hD.1, hD.2.2.1⟩, ?_⟩
    exact takeJ2_after_bitmap (ctxOf p ts) _ tx.base _ v cv L n hpos hJ3' hlk3
      (by show w3.taken.contains L = false; rw [hr03.2.2.1]; exact hLt) (hI.times L n hn)
      (by rw [hr03'.1, hr03'.2.1]; exact keyLeaf_reached hI hrk L hL) hcvN
      (fun y hy => by rw [hr03'.2.2.2.1]; exact (hLV L n hL hn hnl y hy).2) h1 h2 h3 h7
  · have hPOK := pathOK_of_toLeaf (ctxOf p ts) _ w ({ w3 with trail := "up.root-kept-empty" :: w3.trail } : W)
      [] n hI hr03' hp3' hlinkP hlkX
    have hNn : (wNode (ctxOf p ts).p (viewOf (treeRun p ts)) w (nodeAt w.top.rootKey [] 0)).getD
        ⟨true, []⟩ = n := by
      rw [show nodeAt w.top.rootKey [] 0 = L from hXD, hn]; rfl
    have hI3 := putInv_of_readsAs _ _ w _ hI hr03'
    have hG3 := putInvG_of_book _ _ tx.base top _ hB hb3'
    have hinv := delFullRootStepOKT_ctx p ts _ hI3 hG3 (by rw [hr03'.1, hr03'.2.1]; exact hRO) hsa2 _ _ _ hPOK
      pre cv rk hkey (by rw [hr03'.1, hr03'.2.1]; exact hrk)
      (by show (nodeAt w.top.rootKey [] 0, cv) ∈ _; rw [show nodeAt w.top.rootKey [] 0 = L from hXD, hr03'.1]; exact hL)
      (by rw [hr03'.1, hr03'.2.1]; exact hI.keyUniq pre cv rk hkey hrk)
      (by rw [hNn]; exact hnl) (by rw [hNn]; exact hne) (by rw [hNn]; exact hroom)
    have hJ2 := delFullRootJ2OK_ctx p hsa2 ts tx.base _ hI3 hG3 (by rw [hr03'.1, hr03'.2.1]; exact hRO) hJ3'
      (by rw [hr03'.2.2.2.2]; exact hSB) _ _ _ hPOK cv n hNn hnl hne hroom hcvN
    simp only [show nodeAt w.top.rootKey [] 0 = L from hXD] at hinv hJ2
    refine writerWP_mono (writerWP_and (writerWP_and hinv (putBook_appendDeleteKlong L _ cv _ _ tx.base top hB _ hb3'))
      hJ2) ?_
    rintro _ v ⟨⟨⟨hTv, htv, _, _, hreachv, hRv, _⟩, hbv⟩, hJv⟩
    have hun : ∀ y, ReachS (wNode p (viewOf (treeRun p ts)) v) (ts.length + 1) v.top.rootKey y →
        v.taken.contains y = false := by
      intro y hy
      rw [htv]
      rcases hreachv y (reachS_tReach _ _ _ _ hy) with h | h
      · exact hI3.untaken y (tReach_reachS _ _ _ _ h)
      · cases h' : ({ w3 with trail := "up.root-kept-empty" :: w3.trail } : W).taken.contains y with
        | false => rfl
        | true => have := hI3.ids.2.2.1 y h'; dsimp only at this h; omega
    obtain ⟨hPv, _⟩ := putInv_after_step (ctxOf p ts) _ v tx.base top hB hbv hTv hun hRv
    exact ⟨⟨hPv, hRv⟩, hJv.1⟩

/-! ## The stratum's members from the family -/

/-- The family at the stratum's invariant: route P's, its reference left open. -/
abbrev DelStepsTJA (p : Params) (R : Struct BVal → Time → Prop) : Prop :=
  DelStepsCaseTJ p R DelMergeCase (fun ts tx _ _ v => DelInvJAE (ctxOf p ts) (viewOf (treeRun p ts))
    (kindOracleOf p (treeRun p ts)) tx.base tx.base v)

/-- A delete with the merges keeps `QdW` and `TakeJ2`, from a start with no fit and no
heights' bound: the family at `DelInvJAE`, its loops with no fit (FuelNext.lean). -/
theorem qdWJ_delMergeT (p : Params) (R : Struct BVal → Time → Prop) (hS : DelStepsTJA p R)
    (hsa2 : 2 ≤ p.splitAbove) (hcap : 1 ≤ p.mergeMax)
    (hRP : ∀ P t, R P t → PointersOK P) (hRK : ∀ P t, R P t → KindsAllOK p P) :
    ∀ ts tx, Within p (ts ++ [tx]) → R (treeRun p ts) ts.length → ∀ z top,
      lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z →
      topOf p (ctxOf p ts).view z = .ok top →
      ∀ pre op post, tx.ops = pre ++ op :: post →
      ∀ r w, (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
      SJ0 p ts tx w → TakeJ2 (ctxOf p ts) (viewOf (treeRun p ts)) tx.base w →
      DelMergeCase (ctxOf p ts) (viewOf (treeRun p ts)) w op →
      WriterWP (putKv op) (ctxOf p ts) w (fun _ w' =>
        QdW p ts w' ∧ TakeJ2 (ctxOf p ts) (viewOf (treeRun p ts)) tx.base w') := by
  intro ts tx hw hr z top hz htop pre op post hops r w hpre hSw hJ hPc
  obtain ⟨key, hop, hm'⟩ := hPc
  obtain ⟨hv, hk, hICEk⟩ := viewFacts_of_run p R hRP hRK ts tx hw hr
  have hpos : 0 < (ctxOf p ts).i := by simp [ctxOf]
  exact hS ts tx hw hr z top hz htop pre op post hops r w hpre hSw hJ key hop ⟨key, hop, hm'⟩
    (fun v hv' => delInvJAE_of_T _ _ _ _ _ v hv')
    (fun v hv' => ⟨qdW_of_delInvAE p ts _ _ v (delInvAE_of_JAE _ _ _ _ _ v hv'),
      takeJ2_of_delInvJAE _ _ _ _ _ v hv'⟩)
    (fun g h v hv' => writerWP_afterDelete_delJAE key g h (ctxOf p ts) _ (viewCoherent_ctxOf p ts) hpos
      _ _ hv hk hICEk hsa2 hcap tx.base v hv')
    (fun g h merged v hv' => writerWP_mergeUp_delJAE key g (ctxOf p ts) _ (viewCoherent_ctxOf p ts) hpos
      _ _ hv hk hICEk hsa2 hcap tx.base p.fuel h merged v hv')
    (fun seg v hv' => writerWP_collapseRoot_delJAE key seg (ctxOf p ts) _ (viewCoherent_ctxOf p ts)
      _ _ hv hk hICEk hsa2 tx.base hpos v hv')

/-- `opCaseOKJ_treeInvRange_of_qdW` at any start's facts St. -/
theorem opCaseOKJS_treeInvRange_of_qdW (p : Params) (R : Struct BVal → Time → Prop)
    (St : List Tx → Tx → W → Prop)
    (h : OpCaseOKJS p R St (fun ts _ _ w' => QdW p ts w') DelMergeCaseL) :
    OpCaseOKJS p R St (QTree p) DelMergeCaseL ∧ OpCaseOKJS p R St (QPutInv p) DelMergeCaseL ∧
      OpCaseOKJS p R St (QRange p) DelMergeCaseL := by
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

/-- Member (i) of the stratum: the tree, `PutInv` and the ranges after a delete with
the merges, given `StartJ0`, from the family. -/
theorem opCaseOKJ0_treeInvRange_delMergeT (p : Params) (R : Struct BVal → Time → Prop) (hM : 2 ≤ p.M)
    (hS : DelStepsTJA p R) (hsa2 : 2 ≤ p.splitAbove) (hcap : 1 ≤ p.mergeMax)
    (hRP : ∀ P t, R P t → PointersOK P) (hRK : ∀ P t, R P t → KindsAllOK p P) :
    OpCaseOKJS p R (StartJ0 p) (QTree p) DelMergeCaseL ∧ OpCaseOKJS p R (StartJ0 p) (QPutInv p) DelMergeCaseL ∧
      OpCaseOKJS p R (StartJ0 p) (QRange p) DelMergeCaseL := by
  refine opCaseOKJS_treeInvRange_of_qdW p R (StartJ0 p) ?_
  intro ts tx hw hr z top hz htop pre op post hops r w hpre hSt hI hRO hP
  have hSw : SJ0 p ts tx w :=
    ⟨⟨⟨⟨⟨hI, leafVals_reached p hM ts tx hw top pre (op :: post) hops r w hpre (hRP _ _ hr) (hRK _ _ hr)⟩,
      base_le_next_reached p hM ts tx hw top pre (op :: post) hops r w hpre (hRP _ _ hr) (hRK _ _ hr)⟩, hRO⟩,
      hSt.2.2⟩, hSt.1, hP.2⟩
  exact writerWP_mono (qdWJ_delMergeT p R hS hsa2 hcap hRP hRK ts tx hw hr z top hz htop pre op post hops r w
    hpre hSw hSt.2.1 hP.1) (fun _ _ h => h.1)

/-- Member (ii) of the stratum: the take-back's step given `SJ0`, the delete with the
merges from the family, the other cases as in the top theorem. -/
theorem opJ2OK0_of_T (p : Params) (R : Struct BVal → Time → Prop) (hm : p.merges = true) (hM : 2 ≤ p.M)
    (hS : DelStepsTJA p R) (hsa2 : 2 ≤ p.splitAbove) (hcap : 1 ≤ p.mergeMax)
    (hRL : ∀ P t, R P t → RunLinksOK p P t) (hRP : ∀ P t, R P t → PointersOK P)
    (hRK : ∀ P t, R P t → KindsAllOK p P) : OpJ2OK p R (SJ0 p) := by
  have hSI : ∀ ts tx w, SJ0 p ts tx w → PutInv (ctxOf p ts) (viewOf (treeRun p ts)) w :=
    fun _ _ _ h => h.1.1.1.1.1
  have hSV : ∀ ts tx w, SJ0 p ts tx w → LeafVals (ctxOf p ts) (viewOf (treeRun p ts)) tx.base w :=
    fun _ _ _ h => h.1.1.1.1.2
  have hSB : ∀ ts tx w, SJ0 p ts tx w → tx.base ≤ w.next := fun _ _ _ h => h.1.1.1.2
  have hSR : ∀ ts tx w, SJ0 p ts tx w →
      RangeOrder (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey := fun _ _ _ h => h.1.1.2
  exact opJ2OK_of_cases p _ _ (opJ2Case_putLeafRoom p _ _ hSI hSV)
    (opJ2Case_putLeafFull p _ _ hRL hsa2 hSI hSV hSB hSR)
    (opJ2Case_putNewSeg p _ _ hM hSI hSB (opJ2Case_putNewSegFull p _ _ hRL hM hsa2 hSI hSB hSR))
    (fun ts tx hw hr z top hz htop pre op post hops r w hpre _ hSw hJ hP =>
      writerWP_mono (qdWJ_delMergeT p R hS hsa2 hcap hRP hRK ts tx hw hr z top hz htop pre op post hops r w
        hpre hSw hJ hP) (fun _ _ h _ => h.2))
    (opJ2Case_delNoLeaf p _ _ hSI) (opJ2Case_delNoop p _ _ hSI)
    (opJ2CaseOK_void p _ _ _ hm delEmptyCase_merges) (opJ2Case_delRoom p _ _ hSI hSV)
    (opJ2CaseOK_void p _ _ _ hm delFullCase_merges)

/-- The first stratum from the family and `hchk` (bergdb 025-05, step 7): the joint
induction with no `htb`. What is left of step 7 is the family's three cases that
empty the leaf (`DelEmptyM`: room above, the space root, the stop node's cascade) and
`hchk` with no `htb`. -/
theorem jointHtJ_reachedT (p : Params) (R : Struct BVal → Time → Prop) (hm : p.merges = true)
    (hM : 2 ≤ p.M) (hM4 : 4 ≤ p.M) (hsa2 : 2 ≤ p.splitAbove) (hcap : 1 ≤ p.mergeMax)
    (hRB : BaseStartOK p R)
    (hRL : ∀ P t, R P t → RunLinksOK p P t) (hRT : ∀ P t, R P t → TreeAt p P t)
    (hRI : ∀ P t, R P t → InvOK p P t) (hRP : ∀ P t, R P t → PointersOK P)
    (hRK : ∀ P t, R P t → KindsAllOK p P) (hRH : ∀ P t, R P t → HeightAllOK p P t)
    (hTp : OpCaseOK p R (QPut (QTree p)) AnyOp) (hPp : OpCaseOK p R (QPut (QPutInv p)) AnyOp)
    (hOp : OpCaseOK p R (QPut (QRange p)) AnyOp) (hS : DelStepsTJA p R)
    (hLv : OpCaseOK p R (QLive p) AnyOp) (hchk : OpDelChk2ORJ p R)
    (ts : List Tx) (tx : Tx) (hw : Within p (ts ++ [tx])) (hr : R (treeRun p ts) ts.length)
    (z : NodeId) (top : Top)
    (hz : lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z)
    (htop : topOf p (ctxOf p ts).view z = .ok top) :
    ∀ pre post, tx.ops = pre ++ post → ∀ r w,
      (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
      PutInv (ctxOf p ts) (viewOf (treeRun p ts)) w ∧
      RangeOrder (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey ∧
      LiveCounts p (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey ∧
      HtInv (htOracleOf p (treeRun p ts)) tx.base (ctxOf p ts) w ∧
      WriterTreeOK p (treeRun p ts) (ts.length + 1) w ∧ J2At p (treeRun p ts) (ts.length + 1) tx.base w :=
  have hT := opCaseOKJ0_treeInvRange_delMergeT p R hM hS hsa2 hcap hRP hRK
  jointHtJ_reached0 p R hm hM hM4 hRB hRL hRT hRI hRP hRK hRH hTp hPp hOp hT.1 hT.2.1 hT.2.2
    (opJ2OK0_of_T p R hm hM hS hsa2 hcap hRL hRP hRK) hLv hchk ts tx hw hr z top hz htop

end SIS.Tree
