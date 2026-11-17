/-
The contract package (bergdb 030-17): the proofs of RecoverCutTheorems.lean.

* Views that agree but at the root, with the same live children of the root,
  have the same top node, the same space root and are held by the same trees
  (`viewTop_congr`, `viewRoot_congr`, `holdsView_congr`): so a startup from a
  cut stream, whose structure has the view of the run from the first available
  time on but at the root (`SameFrom`), gives Java's readers what the run's
  structure gives.
* The model's structure after transaction k holds, at every time t up to k,
  the top node of time t as the root's live child, with its root pointer and
  skip pointers as written (`MeetsFull.top_view`, from 030-07's `TopInv`).
* Java's readers, on a tree that holds the view and with any top that holds
  the history's top from a time f at or before t, are right at t
  (`MeetsFull.java_reads_from`: 030-14's `java_reads` and `jget_from`).
-/
import Mathlib.Tactic
import Contract.Proof.TopFrom
import Contract.Proof.RecoverTop
import Contract.Proof.BridgeTop
import Contract.Proof.BridgeWords

namespace Contract

open SIS (Struct Entry History Node View Reach)
open SIS.Check (BVal blive)

variable {p : Params} {h : BHist} {top : Nat → Top}

/-! ## Views that agree but at the root -/

theorem viewTop_congr {V1 V2 : View BVal}
    (h0 : (V1 SIS.root).map (fun n => blive n.hist) = (V2 SIS.root).map (fun n => blive n.hist)) :
    viewTop V1 = viewTop V2 := by
  unfold viewTop
  cases h1 : V1 SIS.root <;> cases h2 : V2 SIS.root <;> rw [h1, h2] at h0 <;> simp_all

theorem viewRoot_congr {V1 V2 : View BVal} (hx : ∀ x, x ≠ SIS.root → V1 x = V2 x)
    (h0 : (V1 SIS.root).map (fun n => blive n.hist) = (V2 SIS.root).map (fun n => blive n.hist)) :
    viewRoot V1 = viewRoot V2 := by
  unfold viewRoot
  rw [h0]
  split
  · rename_i z _ _
    split
    · rfl
    · rename_i hz
      rw [hx z hz]
  · rfl

theorem kindOf_congr {V1 V2 : View BVal} (kind : Nat → Bool) (hx : ∀ x, x ≠ SIS.root → V1 x = V2 x) :
    ∀ x, x ≠ SIS.root → kindOf kind V1 x = kindOf kind V2 x := by
  intro x hx0
  simp only [kindOf, hx x hx0]

theorem holdsView_congr {V1 V2 : View BVal} {lf1 lf2 : NodeId → Bool} {t : Time} {s : Tree}
    (hx : ∀ x, x ≠ SIS.root → V1 x = V2 x)
    (h0 : (V1 SIS.root).map (fun n => blive n.hist) = (V2 SIS.root).map (fun n => blive n.hist))
    (hlf : ∀ x, x ≠ SIS.root → lf1 x = lf2 x) (hs : HoldsView V2 lf2 t s) :
    HoldsView V1 lf1 t s := by
  intro x n hx0 hxz hv
  rw [viewTop_congr h0] at hxz
  rw [hx x hx0] at hv
  rw [hlf x hx0]
  exact hs x n hx0 hxz hv

/-! ## The top in the model's structure, at every time -/

theorem rootHist_upTo (tp : Top) (t : Time) :
    History.upTo (rootHist tp) t = rootHist (tp.filter (fun zn => decide (zn.2.time ≤ t))) := by
  unfold History.upTo rootHist
  rw [List.filter_map]
  rfl

theorem topEntries_upTo {n : TopNode} {t : Time} (ht : n.time ≤ t) :
    History.upTo (topEntries n) t = topEntries n := by
  apply SIS.upTo_of_forall
  intro e he
  unfold topEntries at he
  obtain ⟨v, _, rfl⟩ := List.mem_map.mp he
  exact ht

/-- The model's structure after transaction k, at a time t: the root's live
child is the top node of time t, which holds its root pointer and its skip
pointers as written. -/
theorem MeetsFull.top_view (hm : MeetsFull p h top) {k t : Nat} (hk : k ≤ h.txs.length)
    {zn : NodeId × TopNode} (hz : topAt (top k) t = some zn) :
    viewTop (SIS.view h.spec (h.P k) t) = some zn.1 ∧
    ∃ nz, SIS.view h.spec (h.P k) t zn.1 = some nz ∧ nz.hist = topEntries zn.2 := by
  have ti := (hm.meetsBridgeTop.inv k hk).2
  obtain ⟨hm1, hle, _⟩ := topAt_max ti.good hz
  have hroot := ti.rootNode
  have hr0 : Reach h.spec (h.P k) t SIS.root := Reach.root _ hroot
  have hl : ((top k).filter (fun zn => decide (zn.2.time ≤ t))).getLast? = some zn := hz
  have hlive : h.spec.live (History.upTo (rootHist (top k)) t) = [zn.1] := by
    rw [rootHist_upTo]
    obtain ⟨z, n⟩ := zn
    exact blive_rootHist hl
  have hv0 := view_of_reachable ((SIS.reachable_iff _ _ _ _).mpr hr0) hroot
  refine ⟨?_, ?_⟩
  · have hlive' : blive (History.upTo (rootHist (top k)) t) = [zn.1] := hlive
    simp [viewTop, hv0, hlive']
  · obtain ⟨hzn, _, hlt, _⟩ := ti.topNode zn hm1
    have hrz : Reach h.spec (h.P k) t zn.1 :=
      Reach.child hr0 hroot (by rw [hlive]; exact List.mem_singleton_self _) hzn hlt
    have hv := view_of_reachable ((SIS.reachable_iff _ _ _ _).mpr hrz) hzn
    refine ⟨_, hv, ?_⟩
    simp only
    exact topEntries_upTo hle

/-! ## Java's readers from a top that holds the history's top from f -/

/-- For a history that meets `MeetsFull` and K-LEVEL: a tree that holds the
view after transaction k at a time t up to k, read with any top that holds the
history's top after k from a time f at or before t: Java's get and scan at t
are right. -/
theorem MeetsFull.java_reads_from (hm : MeetsFull p h top) (hM : 1 ≤ p.M) {kind : Nat → Bool}
    (hkd : KindsOK kind h) {k t f : Nat} (hk : k ≤ h.txs.length) (htk : t ≤ k) (hft : f ≤ t)
    {s : Tree} {tp : Top} (mid : Bool)
    (hs : HoldsView (SIS.view h.spec (h.P k) t) (kindOf kind (SIS.view h.spec (h.P k) t)) t s)
    (htp : TopFrom f (top k) tp) : JReadsRight s tp t mid (h.txs.map (·.ops)) := by
  have hr := hm.meetsBridge.java_reads hM hkd hk htk hs (hm.findRoot_view hM hk htk mid)
  have hg : TopGood (top k) := (hm.meetsBridgeTop.inv k hk).2.good
  refine ⟨fun key => ?_, fun req hreq limit => ?_⟩
  · rw [jget_from hg htp hft]; exact hr.1 key
  · rw [jscan_from hg htp hft]; exact hr.2 req hreq limit

/-- Java's search from a top that holds the history's top after k from a time
f, at a time t from f to k, finds the space root of the tree after t. -/
theorem MeetsFull.findRoot_from (hm : MeetsFull p h top) (hM : 1 ≤ p.M) {k t f : Nat}
    (hk : k ≤ h.txs.length) (htk : t ≤ k) (hft : f ≤ t) {tp : Top} (htp : TopFrom f (top k) tp)
    (mid : Bool) : findRoot tp t mid = (h.tree t).root := by
  have hg : TopGood (top k) := (hm.meetsBridgeTop.inv k hk).2.good
  rw [Contract.findRoot_from hg htp hft mid, hm.findRoot_view hM hk htk mid,
    hm.meetsBridge.viewRoot_eq hk htk]

end Contract
