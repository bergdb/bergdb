import SIS.Tree.PutInvRun
import SIS.Tree.WriterTreeRoot

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! `PutInv` kept by a delete into a full segment leaf (bergdb 024-12, TP10):
the leaf, which keeps a live klong, full by its size or by its dead klongs
with the bitmap, is replaced by its last version without the key's klong, by a
time split (in place for a leaf that the transaction made, else a new node
that its inner parent's klong names), the merges off. -/

theorem writerWP_replaceOrAdd_nil (last : KNode) (c : Ctx) (w : W) :
    WriterWP (replaceOrAdd last []) c w (fun out v => v = w ∧ out = last) := by
  unfold replaceOrAdd
  simp only [List.foldlM_nil, writerWP_bind, writerWP_read, writerWP_pure]
  exact ⟨trivial, trivial⟩

/-- The time split in place of a node L that the transaction made, with nothing
to insert and a last version `last` given: L holds `last`. -/
theorem writerWP_handleFullWith_timeInPlace_nil (up : NodeId → List (Nat × NodeId) → M Unit)
    (depth : Nat) (L : NodeId) (n last : KNode) (compact : Bool)
    (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base) (w : W)
    (hlk : w.nodes.lookup L = some n) (hLt : w.taken.contains L = false)
    (hfirst : n.firstTime = some c.i)
    (hcs : (!compact && decide (last.size > c.p.splitAbove)) = false) :
    WriterWP (handleFullWith up depth L [] last compact) c w (fun _ w' =>
        w'.taken = w.taken ∧ w'.top = w.top ∧
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
        w'.taken = w.taken ∧ w'.top = w.top ∧
        ∀ y, wNode c.p base w' y = if y = L then some ⟨n.leaf, last.ks⟩ else wNode c.p base w y) := by
    intro w2 hr2 _
    simp only [writerWP_bind]
    refine writerWP_mono (writerWP_replaceOrAdd_nil last c _) ?_
    rintro l w3 ⟨hw3, hl⟩
    subst hw3 hl
    split <;>
    · simp only [note, putNode, writerWP_bind, writerWP_modify]
      refine ⟨hr2.2.2.1, hr2.2.1, ?_⟩
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

/-- The last version of a node without compare value cv: n's live klongs but
cv's, at time t. -/
theorem delLast_facts (n : KNode) (t : Time) (cv : Nat) :
    let last := n.lastVersionGivenDel t (bitsUnion n.lastBitmap (n.bitsOf cv))
    (⟨n.leaf, last.ks⟩ : KNode) = last ∧ (∀ s, Klong.time s ∈ last.ks → s ≤ t) ∧
    ∀ c' z, (c', z) ∈ last.live → (c', z) ∈ n.live := by
  intro last
  refine ⟨rfl, flatAt_times t _ (KNode.lastVersionGivenDel_flatAt n t _), ?_⟩
  intro c' z hz
  have hl := lookup_of_mem_nodup _ (KNode.live_keys_nodup _) c' z hz
  rw [KNode.delete_live_lookup] at hl
  by_cases hc : c' = cv
  · subst hc; simp at hl
  · have hb : (c' == cv) = false := by simpa using hc
    rw [hb] at hl
    simp only [Bool.false_eq_true, ↓reduceIte] at hl
    exact lookup_some_mem hl

end SIS.Tree
