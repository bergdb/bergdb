/-
The merge's parent keeps the dead klongs' bound (bergdb 024-12, a piece for
`QDead` of (4)): `mergeParent` puts the parent in place only when `deadOver`
lets it through (`writerWP_mergeParent_casesD`, `writerWP_mergeParent_cases`
with that fact), and a full parent, or one with too many dead klongs, goes to
`handleFull` (`writerWP_handleFull_lastDead`, `writerWP_handleFull_rootDead`).
-/
import SIS.Tree.DeadSteps
import SIS.Tree.WriterTreeMergeFull

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

set_option linter.unusedSimpArgs false in
/-- `mergeParent` by its two ways, as `writerWP_mergeParent_cases`, with the
fact that the parent in place does not hold too many dead klongs. -/
theorem writerWP_mergeParent_casesD (p : NodeId) (pn : KNode) (depth il cL : Nat) (m1 : NodeId)
    (ir cR : Nat) (m2 : Option (NodeId × Nat)) (c : Ctx) (w : W) (post : Unit → W → Prop)
    (hlk : w.nodes.lookup p = some pn)
    (hroomP : ∀ s : String, deadOver c.p (mergeParentNode pn c.i il cL m1 ir cR m2) = false →
      post () ({ ({ w with trail := s :: w.trail } : W) with
        nodes := upsert w.nodes p (mergeParentNode pn c.i il cL m1 ir cR m2) } : W))
    (hfullP : ∀ (last : KNode) (compact : Bool) (s : String),
      mergeFullLast pn c.i cL m1 cR m2 = some last →
      WriterWP (handleFull depth p last compact) c ({ w with trail := s :: w.trail } : W) post) :
    WriterWP (mergeParent p depth il cL m1 ir cR m2) c w post := by
  cases m2 with
  | none =>
    unfold mergeParent
    simp only [writerWP_bind, writerWP_read]
    rw [writerWP_getNode_known p pn c w hlk]
    apply writerWP_ite_cases
    · intro _
      apply writerWP_ite_cases
      · intro _
        simp only [note, writerWP_bind, writerWP_modify, writerWP_pure]
        split
        · rename_i ks hks
          apply hfullP
          simp only [mergeFullLast] at hks ⊢
          simp only [hks]
        · exact writerWP_throw _ _ _ _
        · exact writerWP_throw _ _ _ _
      · intro hnd
        simp only [note, putNode, writerWP_bind, writerWP_modify]
        exact hroomP _ (Bool.eq_false_iff.mpr hnd)
    · intro _
      simp only [note, writerWP_bind, writerWP_modify, writerWP_pure]
      split
      · rename_i ks hks
        apply hfullP
        simp only [mergeFullLast] at hks ⊢
        simp only [hks]
      · exact writerWP_throw _ _ _ _
      · exact writerWP_throw _ _ _ _
  | some yg =>
    obtain ⟨y, g⟩ := yg
    unfold mergeParent
    simp only [writerWP_bind, writerWP_read]
    rw [writerWP_getNode_known p pn c w hlk]
    apply writerWP_ite_cases
    · intro _
      apply writerWP_ite_cases
      · intro _
        simp only [note, writerWP_bind, writerWP_modify, writerWP_pure]
        split
        · rename_i ks hks
          by_cases hg : g = cR
          · have hgb : (g != cR) = false := by simp [hg]
            simp only [hgb, Bool.false_eq_true, ↓reduceIte, writerWP_bind, writerWP_pure] at hks ⊢
            split
            · rename_i ks2 hks2
              apply hfullP
              simp only [mergeFullLast, hgb, Bool.false_eq_true, ↓reduceIte, hks, hks2]
            · exact writerWP_throw _ _ _ _
            · exact writerWP_throw _ _ _ _
          · have hgb : (g != cR) = true := by simp [hg]
            simp only [hgb, ↓reduceIte] at hks ⊢
            apply hfullP
            simp only [mergeFullLast, hgb, ↓reduceIte, hks]
        · exact writerWP_throw _ _ _ _
        · exact writerWP_throw _ _ _ _
      · intro hnd
        simp only [note, putNode, writerWP_bind, writerWP_modify]
        exact hroomP _ (Bool.eq_false_iff.mpr hnd)
    · intro _
      simp only [note, writerWP_bind, writerWP_modify, writerWP_pure]
      split
      · rename_i ks hks
        by_cases hg : g = cR
        · have hgb : (g != cR) = false := by simp [hg]
          simp only [hgb, Bool.false_eq_true, ↓reduceIte, writerWP_bind, writerWP_pure] at hks ⊢
          split
          · rename_i ks2 hks2
            apply hfullP
            simp only [mergeFullLast, hgb, Bool.false_eq_true, ↓reduceIte, hks, hks2]
          · exact writerWP_throw _ _ _ _
          · exact writerWP_throw _ _ _ _
        · have hgb : (g != cR) = true := by simp [hg]
          simp only [hgb, ↓reduceIte] at hks ⊢
          apply hfullP
          simp only [mergeFullLast, hgb, ↓reduceIte, hks]
      · exact writerWP_throw _ _ _ _
      · exact writerWP_throw _ _ _ _

/-- The merge's parent keeps the bound: in place only when `deadOver` lets it
through; a full parent, or one with too many dead klongs, goes to `handleFull`
(`hfull`, the split and its cascade: `writerWP_handleFull_lastDead`,
`writerWP_handleFull_rootDead`), with the last version `mergeFullLast`. -/
theorem writerWP_mergeParent_dead (p : NodeId) (pn : KNode) (depth il cL : Nat) (m1 : NodeId)
    (ir cR : Nat) (m2 : Option (NodeId × Nat)) (c : Ctx) (base : View BVal) (w : W)
    (hlk : w.nodes.lookup p = some pn) (htk : w.taken.contains p = false)
    (hW : WDeadN c.p (wNode c.p base w))
    (hfull : ∀ (last : KNode) (compact : Bool) (w0 : W), w0.nodes = w.nodes → w0.taken = w.taken →
      mergeFullLast pn c.i cL m1 cR m2 = some last →
      WriterWP (handleFull depth p last compact) c w0 (fun _ w' => WDeadN c.p (wNode c.p base w'))) :
    WriterWP (mergeParent p depth il cL m1 ir cR m2) c w
      (fun _ w' => WDeadN c.p (wNode c.p base w')) := by
  refine writerWP_mergeParent_casesD p pn depth il cL m1 ir cR m2 c w
    (fun _ w' => WDeadN c.p (wNode c.p base w')) hlk ?_ ?_
  · intro s hd
    have hN := wNode_upsert_updN c.p base w
      ({ ({ w with trail := s :: w.trail } : W) with
        nodes := upsert w.nodes p (mergeParentNode pn c.i il cL m1 ir cR m2) } : W) p
      (mergeParentNode pn c.i il cL m1 ir cR m2) rfl rfl htk
    rw [hN]
    exact wDeadN_updN c.p _ p _ hW (fun h0 => deadOver_false c.p _ hd h0)
  · intro last compact s hm
    exact hfull last compact _ rfl rfl hm

end SIS.Tree
