/-
The tree model (bergdb 024-12, TP4 and TP7): the take-back discipline
(`TakeBackOKUnder`, PointersRun.lean) and P's tree (`TreeAt`, WriterTree.lean)
at every run within reach, as one induction over the runs (`runTree_jointJ2`,
TakeBackRunJ2.lean). The circle TP4 → the lift of the writer's overlay → P's
tree → TP4 closes as an induction: each transaction's take-back needs P's tree
before it, and P's tree after it needs the lift, which needs TP4 before it.

The take-back at a transaction's end follows from three facts of its last
state, besides the books (the nodes taken back are made by the transaction;
one overlay entry per node):

* (A) a node reached from the space root is not taken back (`ReachedFree`);
* (B) a kept node with a live klong to a node of the transaction is reached;
* (C) a klong of a kept node to a node taken back comes with a live klong of
  the same node to it (`DeadTakenLive`).

(A) and (B) are tree-level and kept by every operation, with the writer's tree
before and after (prover cost's `OpTreeOK`); (C) holds at a transaction's end.
The induction carries a further statement Q about the runs (`RunTreeQ`), with
its own first state and step, for what the proofs need of P (for example TP7's
invariant). Here: the lift of one transaction (`CommitLiftAt`), (A), (C) and
`RunTreeQ`. TakeBackRunExample.lean computes (A) and (B) and the
writer's tree at every state between operations, and (C) and the take-back at
the last, on two runs whose transactions take nodes back by the upward delete,
by a merge and by root collapse, at the space root and at a segment's.
-/
import SIS.Tree.PointersRun
import SIS.Tree.WriterTree
import SIS.Tree.WriterCacheUnique

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! ## The lift of one transaction -/

/-- The lift of the writer's last state for one transaction: P after it reads
as the writer's nodes (`CommitLiftOK` at one step). -/
def CommitLiftAt (p : Params) (ts : List Tx) (tx : Tx) : Prop :=
  ∀ noops w,
    runOps p tx.base tx.ops (ts.length + 1) (view (treeSpec p) (treeRun p ts) ts.length) =
      .ok (noops, w) →
    (∀ x, knodeOf p (viewOf (treeRun p (ts ++ [tx]))) x = wNode p (viewOf (treeRun p ts)) w x) ∧
    (∀ x ∈ w.taken, tx.base ≤ x) ∧
    (w.newTop = true → w.taken.contains w.top.id = false)

/-- `commitLiftOK_of_overlay` at one transaction, from TP4, the klongs that give
the histories and a history for every key node before it. -/
theorem commitLiftAt_of_links (p : Params) (ts : List Tx) (tx : Tx) (hw : Within p (ts ++ [tx]))
    (hR : RunLinksOK p (treeRun p ts) ts.length) : CommitLiftAt p ts tx := by
  intro noops w hrun
  obtain ⟨hov, htaken, htopt⟩ := overlayLiftOKUnder_links p ts tx hw hR noops w hrun
  refine ⟨?_, htaken, htopt⟩
  have hbase : ∀ q ∈ treeRun p ts, q.1 < tx.base := by
    have h := (hw.2 ts.length (by simp)).1
    have hj : (ts ++ [tx])[ts.length]'(by simp) = tx := by simp
    have ht : (ts ++ [tx]).take ts.length = ts := by simp
    rw [hj, ht] at h
    exact h
  have halloc : AllocatedIds tx.base w := execW_allocatedIds p tx _ _ noops w hrun
  have hmn := madeNodes_of_runOps p ts tx noops w hrun
  obtain ⟨z, top0, _, _, hinv⟩ := commitInv_of_runOps p ts tx noops w hrun
  obtain ⟨_, _, hnt, hvm, _, _⟩ := hinv
  have hroot := treeRun_root p ts
  intro x
  have hov' := hov x
  rw [treeRun_snoc_changes p ts tx noops w hrun] at hov' ⊢
  generalize hP : treeRun p ts = P at hov' hbase hroot ⊢
  generalize hi : ts.length + 1 = i at hov' ⊢
  obtain ⟨ndr, hndr, hlr, hdr⟩ := hroot
  have madeGe : ∀ m ∈ w.made, tx.base ≤ m.id := fun m hm => (halloc.2.2 m hm).1
  by_cases hty : w.taken.contains x = true
  · have hge := htaken x (by simpa using hty)
    have hPx := get?_none_of_ge P tx.base x hbase hge
    have hNx := newNodeOf_changesOf_none i w x (fun m _ hid => by rw [← hid] at hty ⊢; exact hty)
    have hty2 : x ∈ w.taken := by simpa using hty
    simp [knodeOf, viewOf, get?_apply, hPx, hNx, wNode, hty2]
  · have hty' : w.taken.contains x = false := by simpa using hty
    have hty3 : x ∉ w.taken := by simpa using hty
    cases hl : w.nodes.lookup x with
    | some n =>
      rw [hov' n hl hty']
      simp [wNode, hty3, hl]
    | none =>
      have hwn : wNode p (viewOf P) w x = knodeOf p (viewOf P) x := by
        simp [wNode, hty3, hl]
      rw [hwn]
      have hnokey : ∀ q ∈ w.nodes, q.1 ≠ x := by
        intro q hq hqx
        have := List.lookup_eq_none_iff.mp hl q hq
        simp [hqx] at this
      cases hPx : P.get? x with
      | some nd =>
        have hlt : x < tx.base := hbase _ (get?_mem P x nd hPx)
        by_cases hxr : x = root
        · subst hxr
          rw [hndr] at hPx
          cases hPx
          have := rootLevel_gt p
          simp [knodeOf, viewOf, get?_apply_of_get? hndr, hndr, hlr, hdr, this]
        · have hA : addsFor (changesOf i w) i x = [] :=
            List.eq_nil_iff_forall_not_mem.mpr (fun e he => by
              obtain ⟨_, hm⟩ := mem_addsFor.mp he
              rcases mem_changesOf_adds i w x e.val hm with ⟨q, hq, _, hqy⟩ | ⟨h', hh', _⟩ |
                  ⟨hnt', hr⟩
              · exact hnokey q hq hqy
              · have := madeGe _ (hvm _ hh')
                simp only at this
                omega
              · rcases hr with ⟨hxr', _⟩ | ⟨hxt, _⟩
                · exact hxr hxr'
                · obtain ⟨m, hm, hmid, _, _⟩ := hnt hnt'
                  have := madeGe m hm
                  rw [hmid, ← hxt] at this
                  omega)
          simp [knodeOf, viewOf, get?_apply_of_get? hPx, hPx, hA]
      | none =>
        have hk0 : knodeOf p (viewOf P) x = none := by simp [knodeOf, viewOf, hPx]
        rw [hk0]
        cases hNx : newNodeOf (changesOf i w) x with
        | none => simp [knodeOf, viewOf, get?_apply, hPx, hNx]
        | some nd =>
          obtain ⟨m, hm, hid, _, hnd⟩ := newNodeOf_changesOf_some i w x nd hNx
          subst hnd
          cases hmd : m.isData with
          | true => simp [knodeOf, viewOf, get?_apply, hPx, hNx, hmd]
          | false =>
            rcases hmn m hm hmd with hs | hlv
            · rw [hid, hl] at hs
              cases hs
            · have hlv' : p.keyMax < m.level := hlv
              simp [knodeOf, viewOf, get?_apply, hPx, hNx, hmd, hlv']

/-! ## The take-back from three facts of the last state -/

/-- (A) No node reached from the space root is taken back. -/
def ReachedFree (p : Params) (P : Struct BVal) (t : Time) (w : W) : Prop :=
  ∀ y, TReach (wNode p (viewOf P) w) t w.top.rootKey y → w.taken.contains y = false

/-- (C) A klong of a kept overlay node that names a node taken back comes with
a live klong of the same node to it. -/
def DeadTakenLive (t : Time) (w : W) : Prop :=
  ∀ q ∈ w.nodes, w.taken.contains q.1 = false → ∀ cv y, Klong.key cv y ∈ q.2.ks →
    w.taken.contains y = true → ∃ c, (c, y) ∈ q.2.liveAt t

/-! ## The induction over the runs -/

/-- What travels together from one run to the next: TP4 with the klongs that
give the histories and a history for every key node, P's tree, and Q. -/
def RunTreeQ (p : Params) (Q : Struct BVal → Time → Prop) (P : Struct BVal) (t : Time) : Prop :=
  RunLinksOK p P t ∧ TreeAt p P t ∧ Q P t

end SIS.Tree
