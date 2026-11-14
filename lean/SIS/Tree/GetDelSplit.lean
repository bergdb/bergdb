import SIS.Tree.GetSpaceSpace
import SIS.Tree.PutInvDelFull

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! The delete into a full leaf (bergdb 024-12, TP10): the bitmap does not fit,
or the leaf would hold too many dead klongs, and the leaf is time split into
its last version without the key. The reading after it
(`getFromR_timeSplit_del`): the key reads as no value, every other key as
before. -/

/-! ## The writer's time splits with nothing to insert, the values kept -/

/-- `writerWP_handleFullWith_timeInPlace_nil` with the values kept. -/
theorem writerWP_handleFullWith_timeInPlace_nilV (up : NodeId → List (Nat × NodeId) → M Unit)
    (depth : Nat) (L : NodeId) (n last : KNode) (compact : Bool)
    (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base) (w : W)
    (hlk : w.nodes.lookup L = some n) (hLt : w.taken.contains L = false)
    (hfirst : n.firstTime = some c.i)
    (hcs : (!compact && decide (last.size > c.p.splitAbove)) = false) :
    WriterWP (handleFullWith up depth L [] last compact) c w (fun _ w' =>
        w'.taken = w.taken ∧ w'.top = w.top ∧ w'.vals = w.vals ∧
        ∀ y, wNode c.p base w' y = if y = L then some ⟨n.leaf, last.ks⟩ else wNode c.p base w y) := by
  unfold handleFullWith
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known L n c w hlk]
  refine writerWP_ghOf_cached L n c w hlk _ (fun gh => ?_)
  have hnew : (n.firstTime == some c.i) = true := by simp [hfirst]
  simp only [hnew]
  have hpar : WriterWP (parentAt depth) c w (fun _ v => v = w) := by
    unfold parentAt pathNode
    cases depth with
    | zero => simp only [writerWP_pure]
    | succ e =>
      simp only [writerWP_bind, writerWP_get]
      split
      · simp only [writerWP_pure]
      · exact writerWP_throw _ _ _ _
  refine writerWP_mono hpar ?_
  intro a w1 hw1
  subst w1
  have hrest : ∀ w2 : W, ReadsAs c.p base w w2 → w2.nodes.lookup L = some n →
      WriterWP (do
        let l ← replaceOrAdd last []
        if (l.size == 1) = true then do
            note "lone-time-klong"
            putNode L { leaf := n.leaf, ks := l.ks }
          else putNode L { leaf := n.leaf, ks := l.ks }) c w2 (fun _ w' =>
        w'.taken = w.taken ∧ w'.top = w.top ∧ w'.vals = w.vals ∧
        ∀ y, wNode c.p base w' y = if y = L then some ⟨n.leaf, last.ks⟩ else wNode c.p base w y) := by
    intro w2 hr2 _
    simp only [writerWP_bind]
    refine writerWP_mono (writerWP_replaceOrAdd_nil last c _) ?_
    rintro l w3 ⟨hw3, hl⟩
    subst hw3 hl
    split <;>
    · simp only [note, putNode, writerWP_bind, writerWP_modify]
      refine ⟨hr2.2.2.1, hr2.2.1, hr2.2.2.2.1, ?_⟩
      intro y
      by_cases hy : y = L
      · subst hy
        simp only [wNode, hr2.2.2.1, hLt, Bool.false_eq_true, ↓reduceIte, lookup_upsert]
      · rw [← hr2.1]
        simp only [wNode, lookup_upsert, hy, ↓reduceIte]
  simp only [note, writerWP_bind] at hrest
  cases compact with
  | true =>
    simp only [↓reduceIte, note, Bool.not_true, Bool.false_and, Bool.false_eq_true]
    cases a with
    | none =>
      simp only [writerWP_bind, writerWP_pure, writerWP_modify]
      exact hrest _ ⟨rfl, rfl, rfl, rfl, rfl⟩ hlk
    | some q =>
      simp only [writerWP_bind, writerWP_pure, writerWP_modify]
      refine writerWP_mono (writerWP_and (writerWP_getNode_reads q c w base hvc)
        (writerWP_getNode_cache2 q c w)) ?_
      rintro qn w2 ⟨⟨hr2, _, _⟩, ⟨hpre2, _⟩⟩
      have hlk2 : w2.nodes.lookup L = some n := by
        obtain ⟨t, ht⟩ := hpre2
        rw [← ht, List.lookup_append, hlk]; rfl
      exact hrest _ ⟨hr2.1, hr2.2.1, hr2.2.2.1, hr2.2.2.2.1, hr2.2.2.2.2⟩ hlk2
  | false =>
    simp only [Bool.not_false, Bool.true_and] at hcs
    simp only [hcs, ↓reduceIte, note, Bool.not_false, Bool.true_and, Bool.false_eq_true]
    cases a with
    | none =>
      simp only [writerWP_bind, writerWP_pure, writerWP_modify]
      exact hrest _ ⟨rfl, rfl, rfl, rfl, rfl⟩ hlk
    | some q =>
      simp only [writerWP_bind, writerWP_pure, writerWP_modify]
      refine writerWP_mono (writerWP_and (writerWP_getNode_reads q c w base hvc)
        (writerWP_getNode_cache2 q c w)) ?_
      rintro qn w2 ⟨⟨hr2, _, _⟩, ⟨hpre2, _⟩⟩
      have hlk2 : w2.nodes.lookup L = some n := by
        obtain ⟨t, ht⟩ := hpre2
        rw [← ht, List.lookup_append, hlk]; rfl
      exact hrest _ ⟨hr2.1, hr2.2.1, hr2.2.2.1, hr2.2.2.2.1, hr2.2.2.2.2⟩ hlk2

/-! ## The rule: a delete into a leaf below an inner parent with room -/

/-! ## The delete's space split of a full leaf -/

end SIS.Tree
