/-
The books (`PutBook`) across the upward delete's changing steps (bergdb 024-12,
case (4)'s delete steps): the J of `writerWP_deleteUpward_upT_getJMBK`.
-/
import SIS.Tree.TakeDeadUpW
import SIS.Tree.DelStepsWalk

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

theorem state_takeBackX [WriterStateInvariant] (x p : NodeId) (k : Nat) : KeepsState (takeBack x p k) := by
  intro c w hw
  unfold takeBack
  repeat' first
    | siSimplify
    | siDeleteSimplify
    | siCore
    | siAppend
    | wpSplit
    | split
    | contradiction

theorem writerWP_takeBack_freshCacheX (base x p : NodeId) (k : Nat) (c : Ctx) (w : W)
    (hview : ViewIdsBelow base c.view) (hw : FreshCache base w) (hx : x < w.next) :
    WriterWP (takeBack x p k) c w (fun _ v => FreshCache base v ∧ w.next ≤ v.next) := by
  unfold takeBack
  repeat' first
    | wpSimplify
    | frDeleteSimplify
    | frCore base
    | frTake base
    | frAppend base
    | wpSplit
    | split
    | contradiction

theorem putBook_note (s : String) (c : Ctx) (base : View BVal) (B : NodeId)
    (top0 : Top) (hB : PutBase c base B) (w : W) (hw : PutBook c B top0 w) :
    PutBook c B top0 { w with trail := s :: w.trail } := by
  have h := putBook_of_keeps (note s) c base B top0 hB w hw (klongsWf_note s) (good_note B s)
    (book_note B s) (@state_note (allocatedIdsInvariant B) s)
    (@state_note (commitInvariant top0) s) (freshCache_note s) (ptrs_note _ s)
  simp only [note, writerWP_modify] at h
  exact h

theorem putBook_unlink (x : NodeId) (c : Ctx) (base : View BVal) (B : NodeId)
    (top0 : Top) (hB : PutBase c base B) (w : W) (hw : PutBook c B top0 w) :
    WriterWP (unlink x) c w (fun _ w' => PutBook c B top0 w') :=
  putBook_of_keeps _ c base B top0 hB w hw (klongsWf_unlink x) (good_unlink B x) (book_unlink B x)
    (@state_unlink (allocatedIdsInvariant B) x) (@state_unlink (commitInvariant top0) x)
    (freshCache_unlink x) (ptrs_unlink _ x)

theorem putBook_emptyKeyNext (x : NodeId) (d : Nat) (c : Ctx) (base : View BVal) (B : NodeId)
    (top0 : Top) (hB : PutBase c base B) (w : W) (hw : PutBook c B top0 w) :
    WriterWP (emptyKeyNext x d) c w (fun _ w' => PutBook c B top0 w') :=
  putBook_of_keeps _ c base B top0 hB w hw (klongsWf_emptyKeyNext x d) (good_emptyKeyNext B x d)
    (book_emptyKeyNext B x d) (@state_emptyKeyNext (allocatedIdsInvariant B) x d)
    (@state_emptyKeyNext (commitInvariant top0) x d) (freshCache_emptyKeyNext x d) (ptrs_emptyKeyNext _ x d)

theorem putBook_takeBack (x p : NodeId) (k : Nat) (c : Ctx) (base : View BVal) (B : NodeId)
    (top0 : Top) (hB : PutBase c base B) (w : W) (hw : PutBook c B top0 w)
    (hx : ∃ xn, w.nodes.lookup x = some xn) :
    WriterWP (takeBack x p k) c w (fun _ w' => PutBook c B top0 w') := by
  obtain ⟨xn, hl⟩ := hx
  have g1 := klongsWf_takeBack x p k c w hB.wf hw.klongs
  have g2 := good_takeBack B x p k c w hB.good hw.good
  have g3 := book_takeBack B x p k c w w xn hB.good.ids hw.book hl (Kept.refl w)
  have g4 := @state_takeBackX (allocatedIdsInvariant B) x p k c w hw.alloc
  have g5 := @state_takeBackX (commitInvariant top0) x p k c w hw.commit
  have g6 := writerWP_takeBack_freshCacheX B x p k c w hB.good.ids hw.fresh
    (hw.fresh.2.1 (x, xn) (mem_ids_of_lookup _ x xn hl))
  have g7 := ptrs_takeBack (fun y => y < B) x p k c w (putBase_ptrs c base B hB) hw.ptrs
  intro r w' h
  exact ⟨g1 r w' h, g2 r w' h, (g3 r w' h).1, g4 r w' h, g5 r w' h, (g6 r w' h).1, (g7 r w' h).1⟩

end SIS.Tree
