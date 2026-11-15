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
