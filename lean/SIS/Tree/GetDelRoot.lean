import SIS.Tree.GetPutPath
import SIS.Tree.PutInvDelRoot
import SIS.Tree.GetNewRoot

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! The delete of a key of one segment in a space whose root is a leaf (bergdb
024-12, TP10), the merges off: the bitmap in the root with room, or the root
full and split, in time with a new root, or in space with a new root over its
halves, in place for a root the transaction made. The reading after it: the key
reads as no value, every other key as before, when every path inside one segment
tree of the writer's state after it is shorter than the fuel (`SegFits`). -/

/-! ## The writer's splits of the space root for a delete, the values kept -/

/-- `writerWP_handleFullWith_rootSpaceSplit_nil` with the values kept. -/
theorem writerWP_handleFullWith_rootSpaceSplit_nilV (up : NodeId → List (Nat × NodeId) → M Unit)
    (L : NodeId) (n last : KNode) (c : Ctx) (w : W)
    (hlk : w.nodes.lookup L = some n) (hfirst : n.firstTime ≠ some c.i)
    (hsplit : c.p.splitAbove < last.size) (hLn : L < w.next) :
    WriterWP (handleFullWith up 0 L [] last false) c w
      (fun _ w' => RootSpaceSplitNilAfter c w w' L n last ∧ w'.vals = w.vals) := by
  unfold handleFullWith
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known L n c w hlk]
  refine writerWP_ghOf_cached L n c w hlk _ (fun gh => ?_)
  have hnew : (n.firstTime == some c.i) = false := by simpa using hfirst
  have hsz : decide (last.size > c.p.splitAbove) = true := by
    simp only [decide_eq_true_eq, gt_iff_lt]; exact hsplit
  simp only [hnew, parentAt, writerWP_pure, hsz, Bool.not_false, Bool.true_and,
    Bool.false_eq_true, ↓reduceIte]
  have hL1 : L ≠ w.next := by omega
  have hL2 : L ≠ w.next + 2 := by omega
  have hL3 : L ≠ w.next + 2 + 2 := by omega
  simp only [newKey, fresh, setMadeFor, note, putNode, newSuperRoot, writerWP_bind,
    writerWP_modify, writerWP_get, writerWP_set, writerWP_read, writerWP_pure]
  split <;>
  · simp only [writerWP_bind, writerWP_modify, writerWP_pure]
    split <;>
    · simp only [writerWP_bind, writerWP_modify, writerWP_pure]
      split <;>
      · simp only [writerWP_bind, writerWP_modify, writerWP_pure, writerWP_get, writerWP_set]
        refine (writerWP_getNode_known L n c _ ?_ _).mpr ?_
        · simp only [lookup_upsert, List.lookup_append, hL1, hL2, hL3, ↓reduceIte, hlk]
          rfl
        refine ⟨⟨rfl, rfl, ?_⟩, by first | rfl | trivial⟩
        intro x
        simp only [lookup_upsert, List.lookup_append]
        by_cases hxL : x = L
        · subst hxL; simp
        · simp only [hxL, ↓reduceIte]
          by_cases h3 : x = w.next + 2 + 2
          · subst h3
            simp [show w.next + 2 + 2 ≠ w.next by omega]
          · simp only [h3, ↓reduceIte]
            by_cases h2 : x = w.next + 2
            · subst h2; simp
            · simp only [h2, ↓reduceIte]
              by_cases h1 : x = w.next
              · subst h1; simp
              · simp only [h1, ↓reduceIte]
                cases h : w.nodes.lookup x with
                | some m => rfl
                | none =>
                  show (((none : Option KNode).or ([(w.next, { leaf := n.leaf, ks := [] })].lookup x)).or
                    ([(w.next + 2, { leaf := n.leaf, ks := [] })].lookup x)).or
                    ([(w.next + 2 + 2, { leaf := false, ks := [] })].lookup x) = none
                  rw [lookup_cons_ne _ _ _ _ h1, lookup_cons_ne _ _ _ _ h2, lookup_cons_ne _ _ _ _ h3]; rfl

/-- `writerWP_handleFullWith_rootTimeSplit_nil` with the values kept. -/
theorem writerWP_handleFullWith_rootTimeSplit_nilV (up : NodeId → List (Nat × NodeId) → M Unit)
    (L : NodeId) (n last : KNode) (compact : Bool) (c : Ctx) (w : W)
    (hlk : w.nodes.lookup L = some n) (hfirst : n.firstTime ≠ some c.i)
    (hcs : (!compact && decide (last.size > c.p.splitAbove)) = false)
    (hLn : L < w.next) (hny : w.nodes.lookup w.next = none) :
    WriterWP (handleFullWith up 0 L [] last compact) c w (fun _ w' =>
      RootTimeSplitNilAfter c w w' L n last ∧ w'.vals = w.vals) := by
  unfold handleFullWith
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known L n c w hlk]
  refine writerWP_ghOf_cached L n c w hlk _ (fun gh => ?_)
  have hnew : (n.firstTime == some c.i) = false := by simpa using hfirst
  simp only [hnew, parentAt, writerWP_pure, hcs, Bool.false_eq_true, ↓reduceIte, Bool.not_false]
  have hL1 : L ≠ w.next := by omega
  split <;>
  · simp only [note, writerWP_bind, writerWP_modify, writerWP_pure]
    refine writerWP_mono (writerWP_replaceOrAdd_nil last c _) ?_
    rintro l w1 ⟨hw1, hl⟩
    subst w1 hl
    split <;>
    · simp only [newKey, fresh, setMadeFor, note, newSuperRoot, writerWP_bind, writerWP_modify,
        writerWP_get, writerWP_set, writerWP_read, writerWP_pure]
      split <;>
      · simp only [writerWP_bind, writerWP_modify, writerWP_pure]
        split <;>
        · simp only [writerWP_bind, writerWP_modify, writerWP_pure, writerWP_get, writerWP_set]
          refine (writerWP_getNode_known L n c _ ?_ _).mpr ?_
          · simp only [List.lookup_append, hlk]; rfl
          rw [putNode, writerWP_modify]
          refine ⟨⟨rfl, rfl, ?_⟩, by first | rfl | trivial⟩
          intro x
          show (upsert _ L _).lookup x = _
          rw [lookup_upsert]
          by_cases hxL : x = L
          · simp [hxL]
          · simp only [hxL, ↓reduceIte, List.lookup_append]
            by_cases hxy : x = w.next
            · subst hxy; rw [hny]; simp [List.lookup]
            · simp only [hxy, ↓reduceIte]
              cases h : w.nodes.lookup x with
              | some m => rfl
              | none =>
                show (none : Option KNode).or ([(w.next, { leaf := n.leaf, ks := l.ks })].lookup x) = none
                rw [lookup_cons_ne _ _ _ _ hxy]; rfl

set_option linter.unusedSimpArgs false in
/-- `writerWP_handleFullWith_rootSpaceSplitInPlace_nil` with the values kept. -/
theorem writerWP_handleFullWith_rootSpaceSplitInPlace_nilV
    (up : NodeId → List (Nat × NodeId) → M Unit)
    (L : NodeId) (n last : KNode) (c : Ctx) (w : W)
    (hlk : w.nodes.lookup L = some n) (hfirst : n.firstTime = some c.i)
    (hsplit : c.p.splitAbove < last.size) (hLn : L < w.next)
    (hny : w.nodes.lookup (w.next + 2) = none) :
    WriterWP (handleFullWith up 0 L [] last false) c w
      (fun _ w' => RootSpaceSplitInPlaceNilAfter c w w' L n last ∧ w'.vals = w.vals) := by
  unfold handleFullWith
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known L n c w hlk]
  refine writerWP_ghOf_cached L n c w hlk _ (fun gh => ?_)
  have hnew : (n.firstTime == some c.i) = true := by simp [hfirst]
  have hsz : decide (last.size > c.p.splitAbove) = true := by
    simp only [decide_eq_true_eq, gt_iff_lt]; exact hsplit
  simp only [hnew, parentAt, writerWP_pure, hsz, Bool.not_false, Bool.true_and,
    Bool.false_eq_true, ↓reduceIte]
  have hL1 : L ≠ w.next := by omega
  have hL2 : L ≠ w.next + 2 := by omega
  simp only [newKey, fresh, setMadeFor, replacedBy, note, putNode, newSuperRoot, writerWP_bind,
    writerWP_modify, writerWP_get, writerWP_set, writerWP_read, writerWP_pure]
  split <;>
  · simp only [writerWP_bind, writerWP_modify, writerWP_pure]
    split <;>
    · simp only [writerWP_modify, writerWP_pure]
      split <;>
      · simp only [writerWP_bind, writerWP_modify, writerWP_pure, writerWP_get, writerWP_set]
        split <;>
        · simp only [writerWP_bind, writerWP_modify, writerWP_pure, writerWP_get, writerWP_set]
          split <;>
          · simp only [writerWP_bind, writerWP_modify, writerWP_pure, writerWP_get, writerWP_set,
              Bool.not_true, Bool.false_eq_true, ↓reduceIte]
            refine ⟨⟨rfl, rfl, ?_⟩, by first | rfl | trivial⟩
            intro x
            simp only [lookup_upsert, List.lookup_append]
            by_cases hxL : x = L
            · subst hxL; simp [hL1, hL2]
            · simp only [hxL, ↓reduceIte]
              by_cases h1 : x = w.next
              · subst h1; simp
              · simp only [h1, ↓reduceIte]
                by_cases h2 : x = w.next + 2
                · subst h2
                  rw [show w.nodes.lookup (w.next + 2) = none from hny]
                  have hb : (w.next + 2 == w.next) = false := by simp
                  simp [List.lookup, hb]
                · simp only [h2, ↓reduceIte]
                  cases h : w.nodes.lookup x with
                  | some m => rfl
                  | none =>
                    show (((none : Option KNode).or ([(w.next, { leaf := n.leaf, ks := [] })].lookup x)).or
                      ([(w.next + 2, _)].lookup x)) = none
                    rw [lookup_cons_ne _ _ _ _ h1, lookup_cons_ne _ _ _ _ h2]; rfl

end SIS.Tree
