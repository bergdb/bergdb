/-
The books across the merges' steps (bergdb 024-22, case 4): `PutBook` (and so
`PutInvG`, `putInvG_of_book`) is kept by a merge, by the root collapse and by a
node read, from the writer lemmas that every rule keeps the books
(`klongsWf_merge`, `good_merge`, `book_merge`, `state_merge`, `freshCache_merge`,
`ptrs_merge`, and the collapse's and `getNode`'s).
-/
import SIS.Tree.PutInvOK
import SIS.Tree.WriterBookMerge
import SIS.Tree.WriterBookOps
import SIS.Tree.WriterPtrsMerge
import SIS.Tree.WriterPtrsOps
import SIS.Tree.WriterKlongMerge
import SIS.Tree.WriterKlongDelete

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- `PutBook` across a writer action that keeps each of its parts. -/
theorem putBook_of_keeps {α : Type} (f : M α) (c : Ctx) (base : View BVal) (B : NodeId) (top0 : Top)
    (hB : PutBase c base B) (w : W) (hw : PutBook c B top0 w)
    (h1 : KeepsKlongsWf f) (h2 : KeepsGood B f) (h3 : KeepsBook B f)
    (h4 : KeepsStatePred (allocatedIdsInvariant B).pred f)
    (h5 : KeepsStatePred (commitInvariant top0).pred f)
    (h6 : KeepsFreshCache B f) (h7 : KeepsPtrs (fun y => y < B) f) :
    WriterWP f c w (fun _ w' => PutBook c B top0 w') := by
  have g1 := h1 c w hB.wf hw.klongs
  have g2 := h2 c w hB.good hw.good
  have g3 := h3 c w hB.good.ids hw.book
  have g4 := h4 c w hw.alloc
  have g5 := h5 c w hw.commit
  have g6 := h6 c w hB.good.ids hw.fresh
  have g7 := h7 c w (putBase_ptrs c base B hB) hw.ptrs
  intro r w' h
  exact ⟨g1 r w' h, g2 r w' h, (g3 r w' h).1, g4 r w' h, g5 r w' h, (g6 r w' h).1, (g7 r w' h).1⟩

theorem putBook_merge (x : NodeId) (d : Nat) (c : Ctx) (base : View BVal) (B : NodeId) (top0 : Top)
    (hB : PutBase c base B) (w : W) (hw : PutBook c B top0 w) :
    WriterWP (merge x d) c w (fun _ w' => PutBook c B top0 w') :=
  putBook_of_keeps _ c base B top0 hB w hw (klongsWf_merge x d) (good_merge B x d) (book_merge B x d)
    (@state_merge (allocatedIdsInvariant B) x d) (@state_merge (commitInvariant top0) x d)
    (freshCache_merge x d) (ptrs_merge _ x d)

theorem putBook_collapseRoot (key : Key) (seg fuel : Nat) (c : Ctx) (base : View BVal) (B : NodeId)
    (top0 : Top) (hB : PutBase c base B) (w : W) (hw : PutBook c B top0 w) :
    WriterWP (collapseRoot key seg fuel) c w (fun _ w' => PutBook c B top0 w') :=
  putBook_of_keeps _ c base B top0 hB w hw (klongsWf_collapseRoot key seg fuel)
    (good_collapseRoot B key seg fuel) (book_collapseRoot B key seg fuel)
    (@state_collapseRoot (allocatedIdsInvariant B) key seg fuel)
    (@state_collapseRoot (commitInvariant top0) key seg fuel)
    (freshCache_collapseRoot key seg fuel) (ptrs_collapseRoot _ key seg fuel)

theorem putBook_getNode (x : NodeId) (c : Ctx) (base : View BVal) (B : NodeId) (top0 : Top)
    (hB : PutBase c base B) (w : W) (hw : PutBook c B top0 w) :
    WriterWP (getNode x) c w (fun _ w' => PutBook c B top0 w') :=
  putBook_of_keeps _ c base B top0 hB w hw
    (fun c w hv hw => writerWP_mono (klongsWf_getNode x c w hv hw) (fun _ _ h => h.1))
    (fun c w hv hw => writerWP_mono (good_getNode B x c w hv hw) (fun _ _ h => h.1))
    (fun c w hv hb => writerWP_mono (book_getNode B x c w hv hb) (fun _ _ h => ⟨h.1, h.2.1⟩))
    (@state_getNode (allocatedIdsInvariant B) x) (@state_getNode (commitInvariant top0) x)
    (fun c w hv hw => writerWP_mono (writerWP_getNode_freshCache B x c w hv hw)
      (fun _ _ h => ⟨h.1, h.2.1⟩))
    (fun c w hv hw => writerWP_mono (ptrs_getNode _ x c w hv hw) (fun _ _ h => ⟨h.1, h.2.1⟩))

end SIS.Tree
