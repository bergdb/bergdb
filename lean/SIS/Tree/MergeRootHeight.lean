import SIS.Tree.MergeHeightBasics

namespace SIS.Tree

open SIS SIS.Check

/-- Reading a node caches the returned node, appends to the cache, and keeps
the access path. In particular it preserves every earlier cached node. -/
theorem writerWP_getNode_cache (x : NodeId) (c : Ctx) (w : W) :
    WriterWP (getNode x) c w (fun n v =>
      v.nodes.lookup x = some n ∧ w.nodes.IsPrefix v.nodes ∧ v.path = w.path) := by
  unfold getNode
  simp only [writerWP_bind, writerWP_get]
  split
  · rename_i n hn
    simp only [writerWP_pure]
    exact ⟨hn, ⟨[], by simp⟩, trivial⟩
  · rename_i hn
    simp only [writerWP_bind, writerWP_read]
    split
    · split
      · exact writerWP_throw _ _ _ _
      · simp only [writerWP_bind, writerWP_set, writerWP_pure]
        refine ⟨?_, ⟨_, rfl⟩, trivial⟩
        simp [List.lookup_append, hn]
    · exact writerWP_throw _ _ _ _

theorem writerWP_foldlM_state {α β : Type} (xs : List α) (f : β → α → M β)
    (a : β) (c : Ctx) (w : W) (inv : β → W → Prop) (hi : inv a w)
    (step : ∀ a b v, inv a v → WriterWP (f a b) c v inv) :
    WriterWP (xs.foldlM f a) c w inv := by
  induction xs generalizing a w with
  | nil => simpa only [List.foldlM_nil, writerWP_pure] using hi
  | cons b xs ih =>
    rw [List.foldlM_cons, writerWP_bind]
    exact writerWP_mono (step a b w hi) (fun a v hv => ih a v hv)

theorem writerWP_getNode_known (x : NodeId) (n : KNode) (c : Ctx) (w : W)
    (hn : w.nodes.lookup x = some n) (post : KNode → W → Prop) :
    WriterWP (getNode x) c w post ↔ post n w := by
  unfold getNode
  simp only [writerWP_bind, writerWP_get, hn, writerWP_pure]

end SIS.Tree
