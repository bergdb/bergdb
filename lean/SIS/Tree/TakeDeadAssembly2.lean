/-
The take-back's assembly with case (3) split (bergdb 024-12, TP7): a put of a
key with no leaf makes its new segments below a leaf with room (proved,
`writerWP_put_newSegs_j2`), below a full leaf (`PutNewSegFullCase`, open), or
fails. The state predicate `TakeS2` adds that the transaction's first id is at
or below the next id. `PutNewSegFullCase` is latest's (GetOpCases.lean).
-/
import SIS.Tree.TakeDeadNewSeg
import SIS.Tree.GetOpCases

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- The state predicate: `TakeS` and the transaction's first id at or below the
next id. -/
def TakeS2 (p : Params) (ts : List Tx) (tx : Tx) (w : W) : Prop :=
  TakeS p ts tx w ∧ tx.base ≤ w.next

/-- The transaction's first id is at or below the next id at every state between
operations (the books, `kd_ops`). -/
theorem base_le_next_reached (p : Params) (hM : 2 ≤ p.M) (ts : List Tx) (tx : Tx)
    (hw : Within p (ts ++ [tx])) (top : Top) (pre post : List Op) (hsplit : tx.ops = pre ++ post)
    (r : List Bool) (w : W) (h : (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w))
    (hPt : PointersOK (treeRun p ts)) (hK : KindsAllOK p (treeRun p ts)) : tx.base ≤ w.next := by
  have hfresh : ∀ q ∈ treeRun p ts, q.1 < tx.base := by
    have := (hw.2 ts.length (by simp)).1
    simpa using this
  have hwf : tx.wf = true := (hw.1 tx (by simp)).2
  have hkeys : ∀ op ∈ pre, keyWf op.key = true := by
    intro op hop
    unfold Tx.wf at hwf
    exact List.all_eq_true.mp hwf op (by rw [hsplit]; exact List.mem_append_left _ hop)
  have hvk := viewKinds_of p (treeRun p ts) ts.length tx.base hfresh (treeRun_timesLE p ts) hPt hK
  have hkd := kd_ops (kindOracleOf p (treeRun p ts)) tx.base (appendFrameOK tx.base) pre
    (ctxOf p ts) (wInit tx top)
    (viewIdsBelow_rootless _ _ (viewIdsBelow_view p (treeRun p ts) ts.length tx.base hfresh))
    hvk (book_start _ _ top) (kdInv_start _ _ top) hM hkeys r w h
  exact hkd.1.next

/-- (3) from its subcase below a full leaf. -/
theorem opJ2Case_putNewSeg (p : Params) (R : Struct BVal → Time → Prop) (S : List Tx → Tx → W → Prop)
    (hM : 2 ≤ p.M)
    (hSI : ∀ ts tx w, S ts tx w → PutInv (ctxOf p ts) (viewOf (treeRun p ts)) w)
    (hSB : ∀ ts tx w, S ts tx w → tx.base ≤ w.next)
    (hfull : OpJ2CaseOK p R S PutNewSegFullCase) : OpJ2CaseOK p R S PutNewSegCase := by
  intro ts tx hw hr z top hz htop ops op post hops r w hpre hT hS hJ hP
  have hI := hSI ts tx w hS
  obtain ⟨key, h, hop, hno⟩ := hP
  have hkey : keyWf key = true := by
    have := within_op_keyWf p ts tx hw ops _ post hops
    rw [hop] at this; exact this
  have hne : key ≠ [] := by intro h; subst h; simp [keyWf] at hkey
  have hno' : NoLeafFrom (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) p.fuel key
      w.top.rootKey := by
    rintro ⟨pre, cv, rk, L, n, hsplit, hrk, hvis, hn, hnl⟩
    exact hno ⟨pre, cv, L, n, hsplit, rk, hrk, hvis, hn, hnl⟩
  by_cases hseg : NewSegFrom (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) p.fuel key
      w.top.rootKey
  · obtain ⟨pre, c0, tail, rk0, L, n, hk, htail, hrk0, hL, hn, hnl, hnone⟩ := hseg
    subst hk
    by_cases hroom : n.size + 1 < p.M
    · subst hop
      have hone : ∀ L' n', (L', c0) ∈ eqVisits (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1)
          c0 p.fuel rk0 → wNode p (viewOf (treeRun p ts)) w L' = some n' → n'.leaf = true →
          L' = L ∧ n' = n := by
        intro L' n' hL' hn' hnl'
        have he := eqVisits_leaf_unique _ _ _ _ _ _ _ _ _ hL' hL hn' hnl' hn hnl
        subst he
        rw [hn] at hn'
        exact ⟨rfl, (Option.some.inj hn').symm⟩
      refine writerWP_mono (writerWP_put_newSegs_j2 (ctxOf p ts) _ (viewCoherent_ctxOf p ts) pre c0 h
        tail htail rk0 tx.base w hM (by simp [ctxOf]) hrk0 (hI.pathUntaken _) hI.ids hI.fresh
        (fun L' n' hL' hn' hnl' => by
          obtain ⟨_, he2⟩ := hone L' n' hL' hn' hnl'
          rw [he2]
          exact ⟨hI.wf L n hn, hI.times L n hn, hnone, hroom⟩)
        hJ (hSB ts tx w hS) (fun L' hL' => reachS_tReach _ _ _ _ (fromVisits_reach _ _ _ _
          (fun x xn _ hn => hI.wf x xn hn) (pre ++ c0 :: tail) _ L' c0 ReachS.root
          (fromVisits_append_gen _ _ _ c0 tail pre _ rk0 hrk0 _ hL')))) ?_
      intro _ w' h' _
      exact h'
    · exact hfull ts tx hw hr z top hz htop ops op post hops r w hpre hT hS hJ
        ⟨pre, c0, tail, h, rk0, L, n, hop, ⟨htail, hrk0, hL, hn, hnl, hnone⟩, hroom⟩
  · subst hop
    unfold putKv pathClear findRoot pathAdd
    wpSimplify
    generalize hw2 : ({ ({ w with path := [] } : W) with
      path := ([] : List (Option Nat × NodeId)) ++ [(none, w.top.rootKey)] } : W) = w2
    have hr02 : ReadsAs (ctxOf p ts).p (viewOf (treeRun p ts)) w w2 := by
      subst hw2; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
    refine writerWP_mono (writerWP_putSegs_put_fail (ctxOf p ts) _ (viewCoherent_ctxOf p ts) key h
      key w.top.rootKey w2 hne ?_ ?_ ?_) (fun _ _ hf => hf.elim)
    · intro q hq
      rw [hr02.2.2.1]
      rw [hr02.1] at hq
      exact hI.pathUntaken key q hq
    · rw [hr02.1]; exact hno'
    · rw [hr02.1]; exact hseg

/-- TP7's take-back statement with case (3) below a leaf with room proved: open
are (2), (3) below a full leaf, (4), (7), (9). -/
theorem takeBackOK_of_cases2 (p : Params) (hM : 2 ≤ p.M) (Q : Struct BVal → Time → Prop)
    (hQ0 : Q (initStruct p) 0)
    (hQs : ∀ ts tx, Within p (ts ++ [tx]) → RunTreeQ p Q (treeRun p ts) ts.length →
      RunLinksOK p (treeRun p (ts ++ [tx])) (ts.length + 1) →
      TreeAt p (treeRun p (ts ++ [tx])) (ts.length + 1) →
      Q (treeRun p (ts ++ [tx])) (ts.length + 1))
    (hQP : ∀ P t, Q P t → PointersOK P) (hQK : ∀ P t, Q P t → KindsAllOK p P)
    (ho : OpTreeOKUnder p (RunTreeQ p Q))
    (hPI : StateOK p (RunTreeQ p Q) (fun ts _ w => PutInv (ctxOf p ts) (viewOf (treeRun p ts)) w))
    (hB : BaseStartOK p (RunTreeQ p Q))
    (c2 : OpJ2CaseOK p (RunTreeQ p Q) (TakeS2 p) PutLeafFullCase)
    (c3 : OpJ2CaseOK p (RunTreeQ p Q) (TakeS2 p) PutNewSegFullCase)
    (c4 : OpJ2CaseOK p (RunTreeQ p Q) (TakeS2 p) DelMergeCase)
    (c7 : OpJ2CaseOK p (RunTreeQ p Q) (TakeS2 p) DelEmptyCase)
    (c9 : OpJ2CaseOK p (RunTreeQ p Q) (TakeS2 p) DelFullCase) :
    TakeBackOKUnder p (RunLinksOK p) := by
  have hSI : ∀ ts tx w, TakeS2 p ts tx w → PutInv (ctxOf p ts) (viewOf (treeRun p ts)) w :=
    fun _ _ _ h => h.1.1
  have hSV : ∀ ts tx w, TakeS2 p ts tx w → LeafVals (ctxOf p ts) (viewOf (treeRun p ts)) tx.base w :=
    fun _ _ _ h => h.1.2
  have hSB : ∀ ts tx w, TakeS2 p ts tx w → tx.base ≤ w.next := fun _ _ _ h => h.2
  have hS : StateOK p (RunTreeQ p Q) (TakeS2 p) := by
    intro ts tx hw hr z top hz htop pre post hsplit r w h
    exact ⟨⟨hPI ts tx hw hr z top hz htop pre post hsplit r w h,
      leafVals_reached p hM ts tx hw top pre post hsplit r w h (hQP _ _ hr.2.2) (hQK _ _ hr.2.2)⟩,
      base_le_next_reached p hM ts tx hw top pre post hsplit r w h (hQP _ _ hr.2.2) (hQK _ _ hr.2.2)⟩
  have hSRF : ∀ ts tx w, TakeS2 p ts tx w → ReachedFree p (treeRun p ts) (ts.length + 1) w :=
    fun ts _ w h y hy => h.1.1.untaken y (tReach_reachS _ _ _ _ hy)
  have hO : OpJ2OK p (RunTreeQ p Q) (TakeS2 p) :=
    opJ2OK_of_cases p _ _ (opJ2Case_putLeafRoom p _ _ hSI hSV) c2
      (opJ2Case_putNewSeg p _ _ hM hSI hSB c3) c4
      (opJ2Case_delNoLeaf p _ _ hSI) (opJ2Case_delNoop p _ _ hSI) c7 (opJ2Case_delRoom p _ _ hSI hSV) c9
  exact takeBackOK_of_jointJ2 p hM Q hQ0 hQs ho (TakeS2 p) hO hS hSRF hB
    (takenNotValOK_of p hM _ (fun _ _ h => hQP _ _ h.2.2) (fun _ _ h => hQK _ _ h.2.2))

/-- With the merges on: open are (2), (3) below a full leaf, and (4). -/
theorem takeBackOK_of_cases_merges2 (p : Params) (hM : 2 ≤ p.M) (hm : p.merges = true)
    (Q : Struct BVal → Time → Prop) (hQ0 : Q (initStruct p) 0)
    (hQs : ∀ ts tx, Within p (ts ++ [tx]) → RunTreeQ p Q (treeRun p ts) ts.length →
      RunLinksOK p (treeRun p (ts ++ [tx])) (ts.length + 1) →
      TreeAt p (treeRun p (ts ++ [tx])) (ts.length + 1) →
      Q (treeRun p (ts ++ [tx])) (ts.length + 1))
    (hQP : ∀ P t, Q P t → PointersOK P) (hQK : ∀ P t, Q P t → KindsAllOK p P)
    (ho : OpTreeOKUnder p (RunTreeQ p Q))
    (hPI : StateOK p (RunTreeQ p Q) (fun ts _ w => PutInv (ctxOf p ts) (viewOf (treeRun p ts)) w))
    (hB : BaseStartOK p (RunTreeQ p Q))
    (c2 : OpJ2CaseOK p (RunTreeQ p Q) (TakeS2 p) PutLeafFullCase)
    (c3 : OpJ2CaseOK p (RunTreeQ p Q) (TakeS2 p) PutNewSegFullCase)
    (c4 : OpJ2CaseOK p (RunTreeQ p Q) (TakeS2 p) DelMergeCase) :
    TakeBackOKUnder p (RunLinksOK p) :=
  takeBackOK_of_cases2 p hM Q hQ0 hQs hQP hQK ho hPI hB c2 c3 c4
    (opJ2CaseOK_void p _ _ _ hm delEmptyCase_merges) (opJ2CaseOK_void p _ _ _ hm delFullCase_merges)

end SIS.Tree
