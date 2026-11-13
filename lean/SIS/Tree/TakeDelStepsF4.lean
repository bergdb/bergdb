/-
The take-back's delete steps on latest's F3/F4 route (bergdb 024-12, TP7):
`DelStepsJ2OKF3` (the continuations keep `DelInvJF3`) by the delete's cases, the
walks carrying the books and the kinds' books.
-/
import SIS.Tree.TakeDelMergeF4
import SIS.Tree.DelStepsBookK
import SIS.Tree.DelStepsEmptyRoot

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- `DelStepsJ2OKF` on the F3 route: the continuations keep `DelInvJF3`. -/
def DelStepsJ2OKF3 (p : Params) (R : Struct BVal → Time → Prop) (S : List Tx → Tx → W → Prop) : Prop :=
  ∀ ts tx, Within p (ts ++ [tx]) → R (treeRun p ts) ts.length → ∀ z top,
    lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z →
    topOf p (ctxOf p ts).view z = .ok top →
    ∀ pre op post, tx.ops = pre ++ op :: post →
    ∀ r w, (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
    S ts tx w → TakeJ2 (ctxOf p ts) (viewOf (treeRun p ts)) tx.base w →
    ∀ key, op = .del key → p.merges = true →
    (∀ g h v, DelInvJF3 (ctxOf p ts) (viewOf (treeRun p ts)) w key (p.fuel + 1) (kindOracleOf p (treeRun p ts)) tx.base tx.base v →
      WriterWP (afterDelete key g h) (ctxOf p ts) v (fun _ v' => DelInvJF3 (ctxOf p ts) (viewOf (treeRun p ts)) w key (p.fuel + 1) (kindOracleOf p (treeRun p ts)) tx.base tx.base v')) →
    (∀ g h merged v, DelInvJF3 (ctxOf p ts) (viewOf (treeRun p ts)) w key (p.fuel + 1) (kindOracleOf p (treeRun p ts)) tx.base tx.base v →
      WriterWP (mergeUp key g p.fuel h merged) (ctxOf p ts) v (fun _ v' => DelInvJF3 (ctxOf p ts) (viewOf (treeRun p ts)) w key (p.fuel + 1) (kindOracleOf p (treeRun p ts)) tx.base tx.base v')) →
    (∀ seg v, DelInvJF3 (ctxOf p ts) (viewOf (treeRun p ts)) w key (p.fuel + 1) (kindOracleOf p (treeRun p ts)) tx.base tx.base v →
      WriterWP (collapseRoot key seg p.fuel) (ctxOf p ts) v (fun _ v' => DelInvJF3 (ctxOf p ts) (viewOf (treeRun p ts)) w key (p.fuel + 1) (kindOracleOf p (treeRun p ts)) tx.base tx.base v')) →
    WriterWP (putKv op) (ctxOf p ts) w (fun _ w' => TakeJ2 (ctxOf p ts) (viewOf (treeRun p ts)) tx.base w')

/-- `DelStepsJ2OKF3` for the deletes of one case P. -/
def DelStepsCaseJ2OKF3 (p : Params) (R : Struct BVal → Time → Prop) (S : List Tx → Tx → W → Prop)
    (P : Ctx → View BVal → W → Op → Prop) : Prop :=
  ∀ ts tx, Within p (ts ++ [tx]) → R (treeRun p ts) ts.length → ∀ z top,
    lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z →
    topOf p (ctxOf p ts).view z = .ok top →
    ∀ pre op post, tx.ops = pre ++ op :: post →
    ∀ r w, (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
    S ts tx w → TakeJ2 (ctxOf p ts) (viewOf (treeRun p ts)) tx.base w →
    ∀ key, op = .del key → P (ctxOf p ts) (viewOf (treeRun p ts)) w op →
    (∀ g h v, DelInvJF3 (ctxOf p ts) (viewOf (treeRun p ts)) w key (p.fuel + 1) (kindOracleOf p (treeRun p ts)) tx.base tx.base v →
      WriterWP (afterDelete key g h) (ctxOf p ts) v (fun _ v' => DelInvJF3 (ctxOf p ts) (viewOf (treeRun p ts)) w key (p.fuel + 1) (kindOracleOf p (treeRun p ts)) tx.base tx.base v')) →
    (∀ g h merged v, DelInvJF3 (ctxOf p ts) (viewOf (treeRun p ts)) w key (p.fuel + 1) (kindOracleOf p (treeRun p ts)) tx.base tx.base v →
      WriterWP (mergeUp key g p.fuel h merged) (ctxOf p ts) v (fun _ v' => DelInvJF3 (ctxOf p ts) (viewOf (treeRun p ts)) w key (p.fuel + 1) (kindOracleOf p (treeRun p ts)) tx.base tx.base v')) →
    (∀ seg v, DelInvJF3 (ctxOf p ts) (viewOf (treeRun p ts)) w key (p.fuel + 1) (kindOracleOf p (treeRun p ts)) tx.base tx.base v →
      WriterWP (collapseRoot key seg p.fuel) (ctxOf p ts) v (fun _ v' => DelInvJF3 (ctxOf p ts) (viewOf (treeRun p ts)) w key (p.fuel + 1) (kindOracleOf p (treeRun p ts)) tx.base tx.base v')) →
    WriterWP (putKv op) (ctxOf p ts) w (fun _ w' => TakeJ2 (ctxOf p ts) (viewOf (treeRun p ts)) tx.base w')

theorem delStepsJ2OKF3_of_cases (p : Params) (R : Struct BVal → Time → Prop) (S : List Tx → Tx → W → Prop)
    (c5 : DelStepsCaseJ2OKF3 p R S DelNoLeafM) (c6 : DelStepsCaseJ2OKF3 p R S DelNoopM)
    (c7 : DelStepsCaseJ2OKF3 p R S DelEmptyM) (c8 : DelStepsCaseJ2OKF3 p R S DelRoomM)
    (c9 : DelStepsCaseJ2OKF3 p R S DelFullM) : DelStepsJ2OKF3 p R S := by
  intro ts tx hw hr z top hz htop pre op post hops r w hpre hS hJ key hop hm hA hMU hCR
  rcases delMerge_cover (ctxOf p ts) (viewOf (treeRun p ts)) w key hm with h | h | h | h | h
  · exact c5 ts tx hw hr z top hz htop pre op post hops r w hpre hS hJ key hop (hop ▸ h) hA hMU hCR
  · exact c6 ts tx hw hr z top hz htop pre op post hops r w hpre hS hJ key hop (hop ▸ h) hA hMU hCR
  · exact c7 ts tx hw hr z top hz htop pre op post hops r w hpre hS hJ key hop (hop ▸ h) hA hMU hCR
  · exact c8 ts tx hw hr z top hz htop pre op post hops r w hpre hS hJ key hop (hop ▸ h) hA hMU hCR
  · exact c9 ts tx hw hr z top hz htop pre op post hops r w hpre hS hJ key hop (hop ▸ h) hA hMU hCR

theorem delStepsCaseJ2OKF3_or (p : Params) (R : Struct BVal → Time → Prop) (S : List Tx → Tx → W → Prop)
    (P P1 P2 : Ctx → View BVal → W → Op → Prop)
    (hs : ∀ c base w op, P c base w op → P1 c base w op ∨ P2 c base w op)
    (h1 : DelStepsCaseJ2OKF3 p R S P1) (h2 : DelStepsCaseJ2OKF3 p R S P2) : DelStepsCaseJ2OKF3 p R S P := by
  intro ts tx hw hr z top hz htop pre op post hops r w hpre hS hJ key hop hPc hA hMU hCR
  rcases hs _ _ _ _ hPc with h | h
  · exact h1 ts tx hw hr z top hz htop pre op post hops r w hpre hS hJ key hop h hA hMU hCR
  · exact h2 ts tx hw hr z top hz htop pre op post hops r w hpre hS hJ key hop h hA hMU hCR

/-! ## The cases without a continuation -/

/-- No leaf: the take-back. -/
theorem delStepsCaseJ2OKF3_noLeaf (p : Params) (R : Struct BVal → Time → Prop)
    (S : List Tx → Tx → W → Prop)
    (hSI : ∀ ts tx w, S ts tx w → PutInv (ctxOf p ts) (viewOf (treeRun p ts)) w) :
    DelStepsCaseJ2OKF3 p R S DelNoLeafM := by
  intro ts tx hw _ _ _ _ _ ops op post hops _ w _ hS hJ _ _ hP _ _ _
  obtain ⟨key, hop, _, hno⟩ := hP
  subst hop
  have hI := hSI ts tx w hS
  have hkey : keyWf key = true := within_op_keyWf p ts tx hw ops _ post hops
  have hne : key ≠ [] := by intro h; subst h; simp [keyWf] at hkey
  have hno' : NoLeafFrom (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) p.fuel key
      w.top.rootKey := by
    rintro ⟨pre, cv, rk, L, n, hsplit, hrk, hvis, hn, hnl⟩
    exact hno ⟨pre, cv, L, n, hsplit, rk, hrk, hvis, hn, hnl⟩
  exact writerWP_del_noLeaf_j2 (ctxOf p ts) _ (viewCoherent_ctxOf p ts) key tx.base w
    hne (hI.pathUntaken key) hno' hJ

/-- A noop: the take-back. -/
theorem delStepsCaseJ2OKF3_noop (p : Params) (R : Struct BVal → Time → Prop)
    (S : List Tx → Tx → W → Prop)
    (hSI : ∀ ts tx w, S ts tx w → PutInv (ctxOf p ts) (viewOf (treeRun p ts)) w) :
    DelStepsCaseJ2OKF3 p R S DelNoopM := by
  intro ts tx _ _ _ _ _ _ _ op _ _ _ w _ hS hJ _ _ hP _ _ _
  obtain ⟨pre, cv, L, n, hop, _, hK, hnoop⟩ := hP
  subst hop
  have hI := hSI ts tx w hS
  obtain ⟨rk, hrk, _⟩ := keyLeaf_rk hK
  exact writerWP_del_noop_j2 (ctxOf p ts) _ (viewCoherent_ctxOf p ts) pre cv rk tx.base
    w hrk (hI.pathUntaken _) (keyLeaf_all hK hrk (fun m => bitsUnion m.lastBitmap (m.bitsOf cv) = m.lastBitmap)
      hnoop) hJ

set_option maxHeartbeats 1600000 in
/-- The take-back of a delete that empties the leaf at the space root, the merges
on: the root's bitmap (`takeJ2_after_bitmap`), or its split when full
(`delFullRootJ2OK_ctx`). -/
theorem delStepsCaseJ2OKF3_emptyRoot (p : Params) (R : Struct BVal → Time → Prop)
    (S : List Tx → Tx → W → Prop) (hM : 2 ≤ p.M) (hsa2 : 2 ≤ p.splitAbove)
    (hRL : ∀ P t, R P t → RunLinksOK p P t)
    (hP : ∀ ts, Within p ts → PointersOK (treeRun p ts))
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
  obtain ⟨hv, hk, hb0, hi0⟩ := kd_context p hM hP ts tx hw top ops (.del (pre ++ [cv]) :: post) hops r w hpre
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
theorem delStepsCaseJ2OKF3_room (p : Params) (R : Struct BVal → Time → Prop)
    (S : List Tx → Tx → W → Prop) (hM : 2 ≤ p.M)
    (hRL : ∀ P t, R P t → RunLinksOK p P t)
    (hP : ∀ ts, Within p ts → PointersOK (treeRun p ts))
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
  have hICE := innerChildren_reached p hM hP ts tx hw top ops (.del (pre ++ [cv]) :: post) hops r w hpre
    (fun x hx => hI.untaken x (tReach_reachS _ _ _ _ hx))
  have hLV := leafVals_all (hSV ts tx w hS) hkey hrk
  obtain ⟨hv, hk, hb0, hi0⟩ := kd_context p hM hP ts tx hw top ops (.del (pre ++ [cv]) :: post) hops r w hpre
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

set_option maxHeartbeats 1600000 in
/-- The take-back of a delete into a full leaf, the merges on, on the F3 route,
from the fuel premise after the split (`DelFullFitsOK`). -/
theorem delStepsCaseJ2OKF3_full (p : Params) (R : Struct BVal → Time → Prop)
    (S : List Tx → Tx → W → Prop) (hM : 2 ≤ p.M) (hsa2 : 2 ≤ p.splitAbove)
    (hRL : ∀ P t, R P t → RunLinksOK p P t)
    (hP : ∀ ts, Within p ts → PointersOK (treeRun p ts))
    (hSI : ∀ ts tx w, S ts tx w → PutInv (ctxOf p ts) (viewOf (treeRun p ts)) w)
    (hSV : ∀ ts tx w, S ts tx w → LeafVals (ctxOf p ts) (viewOf (treeRun p ts)) tx.base w)
    (hSB : ∀ ts tx w, S ts tx w → tx.base ≤ w.next)
    (hSR : ∀ ts tx w, S ts tx w →
      RangeOrder (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey)
    (hSF : ∀ ts tx w, S ts tx w →
      SegFits (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) (p.fuel - 1) w.top.rootKey)
    (hFits : ∀ ts, DelFullFitsOK (ctxOf p ts) (viewOf (treeRun p ts))) :
    DelStepsCaseJ2OKF3 p R S DelFullM := by
  intro ts tx hw hr z top _ htop ops op post hops r w hpre hS hJ key hop hPc hA _ _
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
  obtain ⟨hv, hk, hb0, hi0⟩ := kd_context p hM hP ts tx hw top ops (.del (pre ++ [cv]) :: post) hops r w hpre
  have hwts : Within p ts := by
    have := within_take p (ts ++ [tx]) hw ts.length
    simpa using this
  have hKall := treeRun_kindsAllOK p hM hP ts hwts
  have hICEk : ICEFromKinds (ctxOf p ts) (viewOf (treeRun p ts)) (kindOracleOf p (treeRun p ts)) tx.base :=
    fun v hb hi hun => innerChildren_of_kinds p (treeRun p ts) tx.base (ctxOf p ts) v rfl hKall
      (hP ts hwts) hb hi.cache hun
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
      (fun v => DelInvJF3 (ctxOf p ts) (viewOf (treeRun p ts)) w (pre ++ [cv]) (p.fuel + 1)
        (kindOracleOf p (treeRun p ts)) tx.base tx.base v) _
      (writerWP_mono (writerWP_and (writerWP_appendDeleteKlong_full_delF3 (ctxOf p ts) _ (viewCoherent_ctxOf p ts)
        (delFullRootStepOK_ctx p ts) (hFits ts) hsa2 _ tx.base hv hk hICEk w pre cv rk tx.base top hB hI hRO hF
        hkey hrk L n P w3 hL hn hnl hne hfull hr03 hJ3 hp3' hlinkP hXD hlkX) hJ2)
        (fun _ v hv' => ⟨hv'.1, hv'.2.1, hv'.2.2⟩)) ?_
    intro g h v hv'
    exact writerWP_mono (hA g h v hv') (fun _ v' hv'' => hv''.2.1)

/-! ## The upward delete with room -/

set_option maxHeartbeats 1600000 in
/-- `writerWP_del_emptyRoomMJ` on the F3 route: the walks carry the kinds' books
too, the continuations keep `DelInvJF3`. -/
theorem writerWP_del_emptyRoomMJK (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (pre : List Nat) (cv : Nat) (rk : NodeId) (w : W) (B : NodeId) (top0 : Top)
    (hB : PutBase c base B) (hbook : PutBook c B top0 w)
    (KO : KindOracle) (BK : NodeId) (hvB : ViewIdsBelow BK c.view) (hk : ViewKinds KO BK c)
    (hb0 : Book BK c w) (hi0 : KdInv KO BK w)
    (hI : PutInv c base w) (hRO : RangeOrder (wNode c.p base w) c.i w.top.rootKey)
    (hF : SegFits (wNode c.p base w) c.i (c.p.fuel - 1) w.top.rootKey)
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
    (hA : ∀ g h v, DelInvJF3 c base w (pre ++ [cv]) (c.p.fuel + 1) KO BK B v →
      WriterWP (afterDelete (pre ++ [cv]) g h) c v (fun _ v' => DelInvJF3 c base w (pre ++ [cv]) (c.p.fuel + 1) KO BK B v'))
    (hMU : ∀ g h merged v, DelInvJF3 c base w (pre ++ [cv]) (c.p.fuel + 1) KO BK B v →
      WriterWP (mergeUp (pre ++ [cv]) g c.p.fuel h merged) c v
        (fun _ v' => DelInvJF3 c base w (pre ++ [cv]) (c.p.fuel + 1) KO BK B v'))
    (hCR : ∀ seg v, DelInvJF3 c base w (pre ++ [cv]) (c.p.fuel + 1) KO BK B v →
      WriterWP (collapseRoot (pre ++ [cv]) seg c.p.fuel) c v
        (fun _ v' => DelInvJF3 c base w (pre ++ [cv]) (c.p.fuel + 1) KO BK B v')) :
    WriterWP (putKv (.del (pre ++ [cv]))) c w (fun _ w' => TakeJ2 c base B w') := by
  have hfuel : 1 ≤ c.p.fuel := by unfold Params.fuel; omega
  refine writerWP_del_toLeafMK c base hvc pre cv rk w (fun v => KdJ c B top0 KO BK v ∧ v.madeFor = w.madeFor)
    ⟨⟨hbook, hb0, hi0⟩, rfl⟩
    (fun s f x v hJ hx => writerWP_mono (writerWP_and (kdJ_descendLte c base B top0 hB KO BK hvB hk s f x v hJ.1 hx)
      (writerWP_descendLte_madeFor s c f x v)) (fun _ v' h => ⟨h.1, h.2.trans hJ.2⟩))
    (fun s x L n v hJ hL hlk hkm => ⟨kdJ_pathAdd c base B top0 hB KO BK hvB s x L n v hJ.1 hL hlk hkm, hJ.2⟩)
    ⟨kdJ_start c base B top0 hB KO BK hvB w ⟨hbook, hb0, hi0⟩, rfl⟩ hrk (hI.pathUntaken _) hI.wf
    (TakeJ2 c base B) (fun v hv => by unfold fresh; wpSimplify; exact hv) ?_
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
  have hfit3 : SegFits (wNode c.p base w3) c.i (c.p.fuel - 1) w3.top.rootKey := by
    rw [hr03.1, hr03.2.1]; exact hF
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
  -- DelInvF at a continuation of the upward delete
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
      PutBook c B top0 w' →
      (∀ key', keyWf key' = true →
        wGet c.p c.i base w' key' = if pre ++ [cv] == key' then none else wGet c.p c.i base w3 key') →
      DelInvF c base w (pre ++ [cv]) (c.p.fuel + 1) w' := by
    intro stop w' sn' f hsD ht htop hv hnodes hsn' hsl' hsw' hst' hlive' hRO' hb' hread
    have hCG := collGetInv_after_upT c base (fun i => nodeAt w.top.rootKey P i)
      (fun i => (wNode c.p base w (nodeAt w.top.rootKey P i)).getD n)
      (fun i => ((P[i - 1]?).bind (·.1)).getD 0) P.length w3 hlkX htk3 hdistP hT3 hwf3 hRt3 hTimesR3
      hICE3 hfit3 hnovalAll3 hreach3 hlinkK stop w' sn' f hsD ht htop hv hnodes hsn' hsl' hsw' hst' hlive'
    exact delInvF_of_collGetInv c base B top0 hB w w3 w' (pre ++ [cv]) hI hF hr03 hCG hRO' hb' hread
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
  refine takeJ2_deleteUpward_upTMBK c base (fun i => nodeAt w.top.rootKey P i)
    (fun i => (wNode c.p base w (nodeAt w.top.rootKey P i)).getD n)
    (fun i => ((P[i - 1]?).bind (·.1)).getD 0) P.length cv pre rk B w3 hdepth hfuel hpos hpX hpK hlkX htk3
    (fun i hi => hTimesR3 _ _ (hreach3 i hi) (hN3 i hi))
    hdistP (by rw [hNnD]; exact hne) (by rw [hNnD]; exact hall) (by rw [hNnD]; exact hnl) hT3 hR3 hwf3 hRt3
    hTimesR3 hICE3 hfit3 hnovalAll3 hreach3
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
  · intro seg stop w' sn' hsD hbetween ht htop hv hnodes hsn' hsl' hsw' hst' hlive' hread _ _ _ hJv _ hb' gs hs
    obtain ⟨hagree, hsnw⟩ := hfr stop w' sn' hsD ht hnodes hsn'
    have hRO' : RangeOrder (wNode c.p base w') c.i w'.top.rootKey := by
      rw [htop]
      exact rangeOrder_up_bitmap (wNode c.p base w3) (wNode c.p base w') c.i w3.top.rootKey _ _ _ stop
        P.length hsD hR3 hT3 (hreach3 stop (by omega)) (fun i _ h2 => hN3 i h2)
        (fun i h1 h2 => hlinkK i (by omega) h2) (fun i i' _ h2 _ h4 he => hdistP i i' h2 h4 he)
        hagree sn' hsnw hsl' (fun c' z h => (hlive' c' z).mp h)
    have hDv := hD stop w' sn' id hsD ht htop hv hnodes hsn' hsl' hsw' hst'
      (fun c' z h => ⟨c', ((hlive' c' z).mp h).1, ((hlive' c' z).mp h).2, rfl⟩) hRO' hb'.1.1 hread
    refine writerWP_mono (hMU gs hs false w' ⟨⟨hDv, hb'.1.2.1, hb'.1.2.2⟩, hJv, hb'.1.1.fresh.1⟩) ?_
    intro _ w1 hD1
    exact writerWP_mono (hCR seg w1 hD1) (fun _ w2 hD2 => hD2.2.1)
  · intro stop w' sn' hsD hbetween ht htop hv hnodes hsn' hsl' hsw' hst' hlive' hread _ _ _ hJv _ hb' gs hs
    obtain ⟨hagree, hsnw⟩ := hfr stop w' sn' hsD ht hnodes hsn'
    have hRO' : RangeOrder (wNode c.p base w') c.i w'.top.rootKey := by
      rw [htop]
      exact rangeOrder_up_bitmap (wNode c.p base w3) (wNode c.p base w') c.i w3.top.rootKey _ _ _ stop
        P.length hsD hR3 hT3 (hreach3 stop (by omega)) (fun i _ h2 => hN3 i h2)
        (fun i h1 h2 => hlinkK i (by omega) h2) (fun i i' _ h2 _ h4 he => hdistP i i' h2 h4 he)
        hagree sn' hsnw hsl' (fun c' z h => (hlive' c' z).mp h)
    have hDv := hD stop w' sn' id hsD ht htop hv hnodes hsn' hsl' hsw' hst'
      (fun c' z h => ⟨c', ((hlive' c' z).mp h).1, ((hlive' c' z).mp h).2, rfl⟩) hRO' hb'.1.1 hread
    exact writerWP_mono (hA gs hs w' ⟨⟨hDv, hb'.1.2.1, hb'.1.2.2⟩, hJv, hb'.1.1.fresh.1⟩) (fun _ w2 hD2 => hD2.2.1)
  · intro seg stop w' sn' jcv jy hsD hbetween ht htop hv hnodes hsn' hsl' hsw' hst' hsl hK0 hj hj0 hmin
      hlive' hread _ _ _ hJv _ hb' gs hs
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
        · exact ⟨c', h1, by omega, by simp [h3]⟩) hRO' hb'.1.1 hread
    refine writerWP_mono (hMU gs hs false w' ⟨⟨hDv, hb'.1.2.1, hb'.1.2.2⟩, hJv, hb'.1.1.fresh.1⟩) ?_
    intro _ w1 hD1
    exact writerWP_mono (hCR seg w1 hD1) (fun _ w2 hD2 => hD2.2.1)

/-- The take-back of a delete whose leaf empties, the upward delete with room,
on the F3 route. -/
theorem delStepsCaseJ2OKF3_emptyRoom (p : Params) (R : Struct BVal → Time → Prop)
    (S : List Tx → Tx → W → Prop) (hM : 2 ≤ p.M)
    (hRL : ∀ P t, R P t → RunLinksOK p P t)
    (hP : ∀ ts, Within p ts → PointersOK (treeRun p ts))
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
  have hICE := innerChildren_reached p hM hP ts tx hw top ops (.del (pre ++ [cv]) :: post) hops r w hpre
    (fun x hx => hI.untaken x (tReach_reachS _ _ _ _ hx))
  have hLV := leafVals_all (hSV ts tx w hS) hkey hrk
  obtain ⟨hv, hk, hb0, hi0⟩ := kd_context p hM hP ts tx hw top ops (.del (pre ++ [cv]) :: post) hops r w hpre
  exact writerWP_del_emptyRoomMJK (ctxOf p ts) _ (viewCoherent_ctxOf p ts) pre cv rk w tx.base top hB hbook
    _ tx.base hv hk hb0 hi0
    hI (hSR ts tx w hS) (hSF ts tx w hS) hICE hkey hrk (keyLeaf_all2 hK hrk _ ⟨hne0, hall0, hup0⟩) hm
    (by simp [ctxOf]) hJ (hSM ts tx w hS) (fun L n hL hn hnl y hy => (hLV L n hL hn hnl y hy).1) hA hMU hCR

/-! ## The case on the F3/F4 route -/

/-- `DelStepsJ2OKF3` with every case proved but the upward delete whose stop node
has no room (`DelEmptyCascM`), and `DelFullFitsOK`. -/
theorem delStepsJ2OKF3_of_open (p : Params) (R : Struct BVal → Time → Prop)
    (S : List Tx → Tx → W → Prop) (hM : 2 ≤ p.M) (hsa2 : 2 ≤ p.splitAbove)
    (hRL : ∀ P t, R P t → RunLinksOK p P t)
    (hP : ∀ ts, Within p ts → PointersOK (treeRun p ts))
    (hSI : ∀ ts tx w, S ts tx w → PutInv (ctxOf p ts) (viewOf (treeRun p ts)) w)
    (hSV : ∀ ts tx w, S ts tx w → LeafVals (ctxOf p ts) (viewOf (treeRun p ts)) tx.base w)
    (hSB : ∀ ts tx w, S ts tx w → tx.base ≤ w.next)
    (hSR : ∀ ts tx w, S ts tx w →
      RangeOrder (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey)
    (hSF : ∀ ts tx w, S ts tx w →
      SegFits (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) (p.fuel - 1) w.top.rootKey)
    (hSM : ∀ ts tx w, S ts tx w → ∀ x o, w.madeFor.lookup x = some o → o < tx.base)
    (c7 : DelStepsCaseJ2OKF3 p R S DelEmptyCascM)
    (hFits : ∀ ts, DelFullFitsOK (ctxOf p ts) (viewOf (treeRun p ts))) :
    DelStepsJ2OKF3 p R S :=
  delStepsJ2OKF3_of_cases p R S (delStepsCaseJ2OKF3_noLeaf p R S hSI) (delStepsCaseJ2OKF3_noop p R S hSI)
    (delStepsCaseJ2OKF3_or p R S _ _ _ delEmptyM_split
      (delStepsCaseJ2OKF3_emptyRoom p R S hM hRL hP hSI hSV hSR hSF hSM)
      (delStepsCaseJ2OKF3_or p R S _ _ _ delEmptyOther_split
        (delStepsCaseJ2OKF3_emptyRoot p R S hM hsa2 hRL hP hSI hSV hSB hSR) c7))
    (delStepsCaseJ2OKF3_room p R S hM hRL hP hSI hSV hSB hSR hSF)
    (delStepsCaseJ2OKF3_full p R S hM hsa2 hRL hP hSI hSV hSB hSR hSF hFits)

/-- (4) A delete with the merges on keeps `J2At` on latest's F4 route: from
`DelStepsJ2OKF3`, `MergeStepOKF3`, `CollapseStepOKF4`, `ReplaceRootFullJ2OK` and
TP4 at every run within reach. -/
theorem opJ2Case_delMergeF4 (p : Params) (R : Struct BVal → Time → Prop) (S : List Tx → Tx → W → Prop)
    (hS : DelStepsJ2OKF3 p R S)
    (hM : ∀ ts, MergeStepOKF3 (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1))
    (hC : ∀ ts, CollapseStepOKF4 (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1))
    (hRJ : ∀ ts B, ReplaceRootFullJ2OK (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1) B)
    (hsa2 : 2 ≤ p.splitAbove) (hcap : 1 ≤ p.mergeMax) (hMM : 2 ≤ p.M)
    (hPtr : ∀ ts, Within p ts → PointersOK (treeRun p ts)) :
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
  have hK := treeRun_kindsAllOK p hMM hPtr ts hwts
  have hv : ViewIdsBelow tx.base (ctxOf p ts).view :=
    viewIdsBelow_rootless _ _ (viewIdsBelow_view p (treeRun p ts) ts.length tx.base hfresh)
  have hk : ViewKinds (kindOracleOf p (treeRun p ts)) tx.base (ctxOf p ts) :=
    viewKinds_of p (treeRun p ts) ts.length tx.base hfresh (treeRun_timesLE p ts) (hPtr ts hwts) hK
  have hICEk : ICEFromKinds (ctxOf p ts) (viewOf (treeRun p ts)) (kindOracleOf p (treeRun p ts)) tx.base :=
    fun v hb hi hun => innerChildren_of_kinds p (treeRun p ts) tx.base (ctxOf p ts) v rfl hK
      (hPtr ts hwts) hb hi.cache hun
  refine writerWP_mono (hS ts tx hw hr z top hz htop pre op post hops r w hpre hSw hJ key hop hmerges
    (fun g h v hv' => writerWP_afterDelete_delJF4 key g h (ctxOf p ts) _ (viewCoherent_ctxOf p ts)
      (p.fuel + 1) hf2 (hM ts) (hC ts) _ _ hv hk hICEk hsa2 hcap tx.base hpos (hRJ ts tx.base) w key v hv')
    (fun g h merged v hv' => writerWP_mergeUp_delJF3 key g (ctxOf p ts) _ (viewCoherent_ctxOf p ts)
      (p.fuel + 1) hf2 (hM ts) _ _ hv hk hICEk hsa2 hcap tx.base hpos w key p.fuel h merged v hv')
    (fun seg v hv' => writerWP_collapseRoot_delJF4 key seg (ctxOf p ts) _ (viewCoherent_ctxOf p ts)
      (p.fuel + 1) hf2 (hC ts) w key _ _ hv hk hICEk hsa2 tx.base hpos (hRJ ts tx.base) v hv')) ?_
  intro _ w' h' _
  exact h'

/-- TP7's take-back statement with the merges on, on latest's F4 route: from
`DelStepsJ2OKF3`, `MergeStepOKF3`, `CollapseStepOKF4`, `ReplaceRootFullJ2OK`,
TP4 at every run within reach and the named run inputs. -/
theorem takeBackOK_of_mergesF4 (p : Params) (hM : 2 ≤ p.M) (hsa : 2 ≤ p.splitAbove)
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
    (hDS : DelStepsJ2OKF3 p (RunTreeQ p Q) (TakeS3 p))
    (hMS : ∀ ts, MergeStepOKF3 (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1))
    (hCo : ∀ ts, CollapseStepOKF4 (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1))
    (hRJ : ∀ ts B, ReplaceRootFullJ2OK (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1) B)
    (hPtr : ∀ ts, Within p ts → PointersOK (treeRun p ts)) :
    TakeBackOKUnder p (RunLinksOK p) :=
  takeBackOK_of_cases_merges4 p hM hsa hm Q hQ0 hQs hQP hQK ho hPI hRO (baseStartOK_runTreeQ p Q)
    (opJ2Case_delMergeF4 p _ _ hDS hMS hCo hRJ hsa hcap hM hPtr)

end SIS.Tree
