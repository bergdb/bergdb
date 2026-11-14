/-
Case (4)'s delete into a full leaf, the merges on (`DelFullM`; bergdb 024-12,
TP7 and TP10): the leaf is replaced by its last version without the key and
splits, with the cascade above, then `afterDelete`. The take-back's facts after
the leaf's bitmap come from `writerWP_appendDeleteKlong_full_j2` for a leaf below
the space root; the leaf at the space root is `DelFullRootJ2OK`
(DelStepsFullRoot.lean), and the delete's invariant after the bitmap is in
DelStepsFullGet.lean.
-/
import SIS.Tree.TakeFullLast
import SIS.Tree.DelStepsEmpty

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- Obligation (the take-back at the space root): a delete's bitmap into the
full leaf that is the space root keeps `TakeJ2` and B at most the next id; it
needs the root's split with the reach-back and the shapes
(`writerWP_handleFull_rootVReach`, latest). -/
def DelFullRootJ2OK (c : Ctx) (base : View BVal) (B : NodeId) : Prop :=
  ∀ (w : W), PutInv c base w → PutInvG c base w → RangeOrder (wNode c.p base w) c.i w.top.rootKey →
    TakeJ2 c base B w → B ≤ w.next →
    ∀ (X : Nat → NodeId) (K : Nat → Nat) (Nn : Nat → KNode), PathOK c w 0 X K Nn →
    ∀ (cv : Nat) (n : KNode), Nn 0 = n → n.leaf = true →
      bitsUnion n.lastBitmap (n.bitsOf cv) ≠ n.lastBitmap → ¬ DelRoom c cv n →
      (∀ y, (cv, y) ∈ n.liveAt c.i → wNode c.p base w y = none) →
      WriterWP (appendDeleteKlong (X 0) 0 cv) c w (fun _ v => TakeJ2 c base B v ∧ B ≤ v.next)

/-- A delete's bitmap into a full leaf at the end of the access path at any
depth keeps `TakeJ2`: below the space root by `writerWP_appendDeleteKlong_full_j2`,
at it by the obligation. -/
theorem writerWP_appendDeleteKlong_full_j2_any (c : Ctx) (base : View BVal) (B : NodeId) (hpos : 0 < c.i)
    (hRoot : DelFullRootJ2OK c base B)
    (w : W) (hI : PutInv c base w) (hG : PutInvG c base w)
    (hRO : RangeOrder (wNode c.p base w) c.i w.top.rootKey)
    (hJ : TakeJ2 c base B w) (hBn : B ≤ w.next) (hsa2 : 2 ≤ c.p.splitAbove)
    (d : Nat) (X : Nat → NodeId) (K : Nat → Nat) (Nn : Nat → KNode) (hP : PathOK c w d X K Nn)
    (cv : Nat) (n : KNode) (hNd : Nn d = n) (hnl : n.leaf = true)
    (hne : bitsUnion n.lastBitmap (n.bitsOf cv) ≠ n.lastBitmap)
    (hfull : ¬ DelRoom c cv n)
    (hcvN : ∀ y, (cv, y) ∈ n.liveAt c.i → wNode c.p base w y = none) :
    WriterWP (appendDeleteKlong (X d) d cv) c w (fun _ v => TakeJ2 c base B v ∧ B ≤ v.next) := by
  cases d with
  | zero => exact hRoot w hI hG hRO hJ hBn X K Nn hP cv n hNd hnl hne hfull hcvN
  | succ D =>
    subst hNd
    exact writerWP_appendDeleteKlong_full_j2 c base B hpos w hI hG hRO hJ hBn hsa2 D X K Nn hP cv hnl hne
      hfull hcvN

/-- The walk's path, cached, as `PathOK` at the state w3 where the walk ends. -/
theorem pathOK_of_toLeaf (c : Ctx) (base : View BVal) (w w3 : W) (P : List (Option Nat × NodeId))
    (n : KNode) (hI : PutInv c base w) (hr03 : ReadsAs c.p base w w3)
    (hp3' : w3.path = (none, w.top.rootKey) :: P)
    (hlinkP : LinkedFrom (wNode c.p base w) c.i w.top.rootKey P)
    (hlkX : ∀ i, i ≤ P.length → w3.nodes.lookup (nodeAt w.top.rootKey P i) =
      some ((wNode c.p base w (nodeAt w.top.rootKey P i)).getD n)) :
    PathOK c w3 P.length (fun i => nodeAt w.top.rootKey P i)
      (fun i => ((P[i - 1]?).bind (·.1)).getD 0)
      (fun i => (wNode c.p base w (nodeAt w.top.rootKey P i)).getD ⟨true, []⟩) := by
  have hpX : ∀ i, i ≤ P.length → (w3.path[i]?).map (·.2) = some (nodeAt w.top.rootKey P i) := by
    intro i hi
    have hl : i < (w.top.rootKey :: P.map (·.2)).length := by simp; omega
    rw [hp3', ← List.getElem?_map, List.map_cons, List.getElem?_eq_getElem hl]
    simp [nodeAt, List.getElem?_eq_getElem hl]
  refine pathOK_of_linked c base w w3 P hr03 hp3' hlinkP ?_
    (fun y hy => hI.untaken y (tReach_reachS _ _ _ _ hy))
  intro e he
  obtain ⟨i, hie⟩ := List.mem_iff_getElem?.mp he
  have hlen : i < w3.path.length := by
    rcases Nat.lt_or_ge i w3.path.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hie; cases hie
  have hi : i ≤ P.length := by rw [hp3'] at hlen; simp at hlen; omega
  have h2 := hpX i hi
  rw [hie] at h2
  simp only [Option.map_some, Option.some.injEq] at h2
  rw [h2]
  exact ⟨_, hlkX i hi⟩

/-- The delete into a full leaf up to `afterDelete` from the walk's end: the
continuation gets the state v after the leaf's bitmap. -/
theorem writerWP_deleteUpward_full (c : Ctx) (L : NodeId) (n : KNode) (d cv : Nat) (key : Key) (w3 : W)
    (hlk3 : w3.nodes.lookup L = some n)
    (hne : bitsUnion n.lastBitmap (n.bitsOf cv) ≠ n.lastBitmap)
    (hkeep : n.allKeysIn (bitsUnion n.lastBitmap (n.bitsOf cv)) = false)
    (Q : W → Prop) (Post : W → Prop)
    (hbit : WriterWP (appendDeleteKlong L d cv) c w3 (fun _ v => Q v))
    (hcont : ∀ g h v, Q v → WriterWP (afterDelete key g h) c v (fun _ v' => Post v')) :
    WriterWP (deleteUpward L d cv key) c w3 (fun _ v => Post v) := by
  unfold deleteUpward
  wpSimplify
  rw [writerWP_getNode_known L n c _ hlk3]
  have hnb : (bitsUnion n.lastBitmap (n.bitsOf cv) == n.lastBitmap) = false := by
    simpa using hne
  simp only [hnb, Bool.false_eq_true, ↓reduceIte, hkeep, Bool.not_false]
  wpSimplify
  refine writerWP_ghOf_cached L n c _ hlk3 _ (fun gh => ?_)
  refine writerWP_mono hbit ?_
  intro _ v hv
  refine writerWP_mono (hcont gh.1 gh.2 v hv) ?_
  intro _ v' hv'
  try simp only [writerWP_pure]
  exact hv'

/-! ## The two obligations with the full leaf reduced -/

end SIS.Tree
