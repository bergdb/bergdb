import SIS.Tree.WriterKlongDelete
import SIS.Tree.PhysicalSelection

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- The next child selected after excluding the empty key is still live in
the original bitmap. Deleting it therefore grows that bitmap strictly. -/
theorem KNode.nextPhysical_delete_changes (n : KNode) (i cv : Nat) (y : NodeId)
    (hchoice : n.ks.zipIdx.foldl
      (nextPhysicalStep (bitsUnion n.lastBitmap (n.bitsOf 0))) none = some (i, cv, y)) :
    bitsUnion n.lastBitmap (n.bitsOf cv) ≠ n.lastBitmap := by
  have hh := nextPhysical_live n.ks (bitsUnion n.lastBitmap (n.bitsOf 0)) i cv y hchoice
  apply n.delete_bitmap_changes_of_physical cv i y
  refine ⟨hh.1, ?_⟩
  intro hi
  exact hh.2 ((mem_bitsUnion_iff _ _ _).mpr (Or.inl hi))

/-- LE-b's room update: delete the next separator and repoint or append
the empty-key pointer. Both bitmap modes preserve physical history. -/
theorem KNode.leb_write_wf (n : KNode) (t : Time) (cv : Nat) (y : NodeId)
    (e : Nat) (inPlace : Bool) (hw : klongsWf n.ks = true)
    (hc : bitsUnion n.lastBitmap (n.bitsOf cv) ≠ n.lastBitmap) :
    let hasTransDel := (match n.ks.getLast? with | some (.del _) => true | _ => false) &&
      n.lastTime == some t
    let union := bitsUnion n.lastBitmap (n.bitsOf cv)
    let n1 := if hasTransDel then n.setAt (n.size - 1) (.del union) else n.add t (.del union)
    klongsWf (if inPlace then n1.repoint e y else n1.add t (.key 0 y)).ks = true := by
  dsimp only
  have hset (hf : ((match n.ks.getLast? with | some (.del _) => true | _ => false) &&
      n.lastTime == some t) = true) := n.setAt_delete_wf_of_flag t cv hw hf
  have hadd := n.add_delete_wf t cv hw hc
  have hbase : klongsWf (if
      ((match n.ks.getLast? with | some (.del _) => true | _ => false) &&
        n.lastTime == some t) then
      n.setAt (n.size - 1) (.del (bitsUnion n.lastBitmap (n.bitsOf cv))) else
      n.add t (.del (bitsUnion n.lastBitmap (n.bitsOf cv)))).ks = true := by
    by_cases hflag : ((match n.ks.getLast? with | some (.del _) => true | _ => false) &&
      n.lastTime == some t) = true
    · simp only [hflag, ↓reduceIte]
      exact hset hflag
    · simp only [hflag, ↓reduceIte]
      exact hadd
  cases inPlace with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact KNode.add_key_wf _ _ _ _ hbase
  | true =>
    simp only [↓reduceIte]
    rw [KNode.repoint_klongsWf]
    exact hbase

macro "kwLebStore" : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (putNode _ _) _ _ _)
  (with_unfolding_none refine writerWP_of_klongsWf (klongsWf_putNode _ _ ?kwInput) _ _ _ ?kwView ?kwState ?kwPost)
  case kwInput =>
    apply KNode.leb_write_wf
    · assumption
    · apply KNode.nextPhysical_delete_changes; assumption
  case kwView => assumption
  case kwState => assumption
  intro _ _ _))

macro "kwLebFull" : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (handleFull _ _ _ _) _ _ _)
  (with_unfolding_none refine writerWP_of_klongsWf (klongsWf_handleFull _ _ _ _ ?kwLast) _ _ _ ?kwView ?kwState ?kwPost)
  case kwLast =>
    apply flatKlongs_rename_after_head
    · assumption
    · exact KNode.lastVersionGivenDel_flat _ _ _
  case kwView => assumption
  case kwState => assumption
  intro _ _ _))

set_option maxHeartbeats 1400000 in
/-- The complete LE-b writer preserves well-formed cached histories,
including both pointer modes, both bitmap modes, space/time replacement
and dead compaction. Only old cached/readable well-formedness is assumed. -/
theorem klongsWf_emptyKeyNext (x : NodeId) (depth : Nat) :
    KeepsKlongsWf (emptyKeyNext x depth) := by
  intro c w hv hw
  unfold emptyKeyNext
  repeat' first
    | wpSimplify
    | kwCore
    | kwLebStore
    | kwLebFull
    | wpSplit
    | split
    | contradiction

end SIS.Tree
