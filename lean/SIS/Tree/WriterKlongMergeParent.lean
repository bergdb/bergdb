import SIS.Tree.WriterKlongLEB
import SIS.Tree.MergeHeightBasics

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- The merge parent's room update preserves physical history. The left
and right pointer modes may be arbitrary; a real deletion must grow its
bitmap, which follows from selecting a live right separator. -/
theorem KNode.merge_writes_wf (n : KNode) (t : Time) (il cL : Nat) (m1 : NodeId)
    (ir cR : Nat) (m2 : Option (NodeId × Nat)) (lInPlace rInPlace : Bool)
    (hw : klongsWf n.ks = true)
    (hc : bitsUnion n.lastBitmap (n.bitsOf cR) ≠ n.lastBitmap) :
    let deleteR := match m2 with | some (_, g) => g != cR | none => true
    let hasTransDel := (match n.ks.getLast? with | some (.del _) => true | _ => false) &&
      n.lastTime == some t
    let union := if deleteR then bitsUnion n.lastBitmap (n.bitsOf cR) else n.lastBitmap
    let n1 := if !deleteR then n else if hasTransDel then n.setAt (n.size - 1) (.del union)
      else n.add t (.del union)
    let n2 := if lInPlace then n1.repoint il m1 else n1.add t (.key cL m1)
    let n3 := match m2 with
      | some (y, g) => if rInPlace then n2.repoint ir y
        else n2.add t (.key (if deleteR then g else cR) y)
      | none => n2
    klongsWf n3.ks = true := by
  dsimp only
  generalize hd : (match m2 with | some (_, g) => g != cR | none => true) = deleteR
  have hbase : klongsWf (if !deleteR then n else if
      ((match n.ks.getLast? with | some (.del _) => true | _ => false) &&
        n.lastTime == some t) then
      n.setAt (n.size - 1)
        (.del (if deleteR then bitsUnion n.lastBitmap (n.bitsOf cR) else n.lastBitmap))
      else n.add t
        (.del (if deleteR then bitsUnion n.lastBitmap (n.bitsOf cR) else n.lastBitmap))).ks = true := by
    cases deleteR with
    | false => simpa only [Bool.not_false, ↓reduceIte] using hw
    | true =>
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      by_cases hf : ((match n.ks.getLast? with | some (.del _) => true | _ => false) &&
        n.lastTime == some t) = true
      · simp only [hf, ↓reduceIte]
        exact n.setAt_delete_wf_of_flag t cR hw hf
      · simp only [hf, ↓reduceIte]
        exact n.add_delete_wf t cR hw hc
  have hleft : klongsWf (if lInPlace then
      (if !deleteR then n else if
          ((match n.ks.getLast? with | some (.del _) => true | _ => false) &&
            n.lastTime == some t) then
          n.setAt (n.size - 1)
            (.del (if deleteR then bitsUnion n.lastBitmap (n.bitsOf cR) else n.lastBitmap))
        else n.add t
          (.del (if deleteR then bitsUnion n.lastBitmap (n.bitsOf cR) else n.lastBitmap))).repoint il m1
      else (if !deleteR then n else if
          ((match n.ks.getLast? with | some (.del _) => true | _ => false) &&
            n.lastTime == some t) then
          n.setAt (n.size - 1)
            (.del (if deleteR then bitsUnion n.lastBitmap (n.bitsOf cR) else n.lastBitmap))
        else n.add t
          (.del (if deleteR then bitsUnion n.lastBitmap (n.bitsOf cR) else n.lastBitmap))).add t (.key cL m1)).ks = true := by
    cases lInPlace with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact KNode.add_key_wf _ _ _ _ hbase
    | true =>
      simp only [↓reduceIte, KNode.repoint_klongsWf]
      exact hbase
  cases m2 with
  | none => exact hleft
  | some pair =>
    rcases pair with ⟨y, g⟩
    dsimp only
    cases rInPlace with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact KNode.add_key_wf _ _ _ _ hleft
    | true =>
      simp only [↓reduceIte, KNode.repoint_klongsWf]
      exact hleft

macro "kwMergeStore" : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (putNode _ _) _ _ _)
  (with_unfolding_none refine writerWP_of_klongsWf (klongsWf_putNode _ _ ?kwInput) _ _ _ ?kwView ?kwState ?kwPost)
  case kwInput => apply KNode.merge_writes_wf <;> assumption
  case kwView => assumption
  case kwState => assumption
  intro _ _ _))

set_option maxHeartbeats 1600000 in
/-- Every successful merge-parent update preserves physical histories,
including its time/space-split recursion. The right separator must be live
in the cached input parent; no sorted-range or size premise is needed. -/
theorem writerWP_mergeParent_wf (q : NodeId) (pn : KNode) (depth il cL : Nat)
    (m1 : NodeId) (ir cR : Nat) (m2 : Option (NodeId × Nat)) (c : Ctx) (w : W)
    (hv : ViewKlongsWf c.p c.view) (hw : WriterKlongsWf w)
    (hp : w.nodes.lookup q = some pn) (hR : cR ∈ pn.live.map Prod.fst) :
    WriterWP (mergeParent q depth il cL m1 ir cR m2) c w
      (fun _ v => WriterKlongsWf v) := by
  have hpn := writerKlongsWf_lookup w hw q pn hp
  have hchange := pn.delete_bitmap_changes_of_live cR hR
  unfold mergeParent
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known q pn c w hp]
  repeat' first
    | wpSimplify
    | kwCore
    | kwMergeStore
    | kwHandle
    | wpSplit
    | split
    | contradiction

end SIS.Tree
