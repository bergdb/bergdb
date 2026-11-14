import SIS.Tree.PutInvDelFull
import SIS.Tree.GetInnerSplit
import SIS.Tree.GetSpaceSpace

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! `PutInv` kept by every delete of a key of one segment in a space whose root
is a leaf (bergdb 024-12, TP10), the merges off: no value, a bitmap with room,
the root kept empty (the upward delete's first case), the root full by its
size or its dead klongs split in time or in space, in place for a root the
transaction made (`putInv_del_leafRoot`). -/

/-! ## The space root's splits with nothing to insert (a delete) -/

/-- The state after a space split of the space root L with nothing to insert
and the last version `last`: the halves at the next two ids under a new root
at the id after them, which the super root names; L keeps its klongs before. -/
def RootSpaceSplitNilAfter (c : Ctx) (w w' : W) (L : NodeId) (n last : KNode) : Prop :=
  w'.taken = w.taken ∧ w'.top.rootKey = w.next + 2 + 2 ∧
    ∀ x, w'.nodes.lookup x =
      if x = L then some (n.toPrev (c.i - 1))
      else if x = w.next then some (halves n.leaf c.i last []).1
      else if x = w.next + 2 then some (halves n.leaf c.i last []).2.1
      else if x = w.next + 2 + 2 then some ⟨false, [.time c.i, .key 0 w.next,
        .key (halves n.leaf c.i last []).2.2 (w.next + 2)]⟩
      else w.nodes.lookup x

/-- The state after a time split of the space root L with the last version
`last`: a new root at the next id holds it. -/
def RootTimeSplitNilAfter (c : Ctx) (w w' : W) (L : NodeId) (n last : KNode) : Prop :=
  w'.taken = w.taken ∧ w'.top.rootKey = w.next ∧
    ∀ x, w'.nodes.lookup x =
      if x = L then some (n.toPrev (c.i - 1))
      else if x = w.next then some ⟨n.leaf, last.ks⟩ else w.nodes.lookup x

/-- The state after a space split in place of the space root L with nothing to
insert: L the first half, the next id the second, the id after the new root. -/
def RootSpaceSplitInPlaceNilAfter (c : Ctx) (w w' : W) (L : NodeId) (n last : KNode) : Prop :=
  w'.taken = w.taken ∧ w'.top.rootKey = w.next + 2 ∧
    ∀ x, w'.nodes.lookup x =
      if x = L then some (halves n.leaf c.i last []).1
      else if x = w.next then some (halves n.leaf c.i last []).2.1
      else if x = w.next + 2 then some ⟨false, [.time c.i, .key 0 L,
        .key (halves n.leaf c.i last []).2.2 w.next]⟩
      else w.nodes.lookup x

theorem writerWP_handleFullWith_rootSpaceSplit_nil (up : NodeId → List (Nat × NodeId) → M Unit)
    (L : NodeId) (n last : KNode) (c : Ctx) (w : W)
    (hlk : w.nodes.lookup L = some n) (hfirst : n.firstTime ≠ some c.i)
    (hsplit : c.p.splitAbove < last.size) (hLn : L < w.next) :
    WriterWP (handleFullWith up 0 L [] last false) c w
      (fun _ w' => RootSpaceSplitNilAfter c w w' L n last) := by
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
        refine ⟨rfl, rfl, ?_⟩
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

theorem writerWP_handleFullWith_rootTimeSplit_nil (up : NodeId → List (Nat × NodeId) → M Unit)
    (L : NodeId) (n last : KNode) (compact : Bool) (c : Ctx) (w : W)
    (hlk : w.nodes.lookup L = some n) (hfirst : n.firstTime ≠ some c.i)
    (hcs : (!compact && decide (last.size > c.p.splitAbove)) = false)
    (hLn : L < w.next) (hny : w.nodes.lookup w.next = none) :
    WriterWP (handleFullWith up 0 L [] last compact) c w (fun _ w' =>
      RootTimeSplitNilAfter c w w' L n last) := by
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
          refine ⟨rfl, rfl, ?_⟩
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

theorem writerWP_handleFullWith_rootSpaceSplitInPlace_nil
    (up : NodeId → List (Nat × NodeId) → M Unit)
    (L : NodeId) (n last : KNode) (c : Ctx) (w : W)
    (hlk : w.nodes.lookup L = some n) (hfirst : n.firstTime = some c.i)
    (hsplit : c.p.splitAbove < last.size) (hLn : L < w.next)
    (hny : w.nodes.lookup (w.next + 2) = none) :
    WriterWP (handleFullWith up 0 L [] last false) c w
      (fun _ w' => RootSpaceSplitInPlaceNilAfter c w w' L n last) := by
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
            refine ⟨rfl, rfl, ?_⟩
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
