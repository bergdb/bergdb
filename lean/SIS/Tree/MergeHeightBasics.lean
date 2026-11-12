import SIS.Tree.WriterGrowth

namespace SIS.Tree

open SIS SIS.Check

/-- All heights seen by the writer are at most cap. -/
def SeenHeightBound (cap : Nat) (w : W) : Prop :=
  ∀ x g h, (x, g, h) ∈ w.gh → h ≤ cap

theorem seenHeightBound_of_sublist {cap : Nat} {w v : W}
    (hsub : w.gh.Sublist v.gh) (hv : SeenHeightBound cap v) : SeenHeightBound cap w := by
  intro x g h hm
  exact hv x g h (hsub.subset hm)

theorem writerWP_of_result {α : Type} (f : M α) (c : Ctx) (w : W) (post : α → W → Prop)
    (hp : ∀ r v, f c w = .ok (r, v) → post r v) : WriterWP f c w post := hp

macro "wpTrace" : tactic => `(tactic| (
  (with_unfolding_none refine writerWP_of_result _ _ _ _ ?_)
  intro _ _ _))

theorem gh_lookup_mem {ns : List (NodeId × Nat × Nat)} {x g h : Nat}
    (hm : ns.lookup x = some (g, h)) : (x, g, h) ∈ ns := by
  obtain ⟨a, b, he, _⟩ := List.lookup_eq_some_iff.mp hm
  rw [he]
  simp

theorem writerWP_of_stats {α : Type} {f : M α} {k : Nat}
    (hc : MergesLe k f) (hg : FieldsGrow f) (c : Ctx) (w : W) (post : α → W → Prop)
    (hp : ∀ r v, f c w = .ok (r, v) → v.merges ≤ w.merges + k →
      w.gh.Sublist v.gh → post r v) : WriterWP f c w post := by
  intro r v hr
  exact hp r v hr (hc c w v r hr) (hg c w r v hr).1

theorem writerWP_of_frame_growth {α : Type} {f : M α} {k : Nat}
    (hc : MergesLe k f) (hg : FieldsGrow f) (c : Ctx) (w : W) (post : α → W → Prop)
    (hp : ∀ r v, v.merges ≤ w.merges + k → w.gh.Sublist v.gh → post r v) :
    WriterWP f c w post := by
  intro r v hr
  exact hp r v (hc c w v r hr) (hg c w r v hr).1

theorem writerWP_of_bounded {α : Type} {f : M α} {c : Ctx} {w : W}
    {post : α → W → Prop} (hf : WriterWP f c w post) (hg : FieldsGrow f)
    (post' : α → W → Prop)
    (hp : ∀ r v, post r v → w.gh.Sublist v.gh → post' r v) : WriterWP f c w post' := by
  intro r v hr
  exact hp r v (hf r v hr) (hg c w r v hr).1

macro "whUse " hc:term " using " hf:term : tactic => `(tactic| (
  (with_unfolding_none refine writerWP_of_frame_growth $hc (by growthFrom $hf) _ _ _ ?_)
  intro _ _ _ _))

macro "whBound " hc:term " using " hf:term : tactic => `(tactic| (
  (with_reducible refine writerWP_of_bounded $hc (by growthFrom $hf) _ ?_)
  intro _ _ _ _))

macro "whFrame" : tactic => `(tactic| first
  | exact writerWP_throw _ _ _ _
  | whUse (mergesLe_getNode 0 _) using (fields_getNode _)
  | whUse (mergesLe_ghOf _) using (fields_ghOf _)
  | whUse (mergesLe_fresh 0) using (fields_fresh)
  | whUse (mergesLe_note 0 _) using (fields_note _)
  | whUse (mergesLe_newKey _ _ _ _) using (fields_newKey _ _ _ _)
  | whUse (mergesLe_newValue _) using (fields_newValue _)
  | whUse (mergesLe_putNode _ _) using (fields_putNode _ _)
  | whUse (mergesLe_setMadeFor _ _) using (fields_setMadeFor _ _)
  | whUse (mergesLe_replacedBy _) using (fields_replacedBy _)
  | whUse (mergesLe_takenBack _) using (fields_takenBack _)
  | whUse (mergesLe_pathClear) using (fields_pathClear)
  | whUse (mergesLe_pathAdd _ _) using (fields_pathAdd _ _)
  | whUse (mergesLe_pathSize) using (fields_pathSize)
  | whUse (mergesLe_pathNode _) using (fields_pathNode _)
  | whUse (mergesLe_klongAt _) using (fields_klongAt _)
  | whUse (mergesLe_parentAt _) using (fields_parentAt _)
  | whUse (mergesLe_newSuperRoot _) using (fields_newSuperRoot _)
  | whUse (mergesLe_replaceOrAdd _ _) using (fields_replaceOrAdd _ _)
  | whUse (mergesLe_appendKlongs _ _ _) using (fields_appendKlongs _ _ _)
  | whUse (mergesLe_handleFull _ _ _) using (fields_handleFull _ _ _)
  | whUse (mergesLe_unlink _) using (fields_unlink _)
  | whUse (mergesLe_retarget _ _ _) using (fields_retarget _ _ _)
  | whUse (mergesLe_descendLte _ _ _) using (fields_descendLte _ _ _)
  | whUse (mergesLe_descendToSegmentRoot _ _) using (fields_descendToSegmentRoot _ _)
  | whUse (mergesLe_descendToHeight _ _ _) using (fields_descendToHeight _ _ _)
  | whUse (mergesLe_collapseRoot _ _ _) using (fields_collapseRoot _ _ _)
  | whUse (mergesLe_climb _) using (fields_climb _)
  | whUse (mergesLe_appendDeleteKlong _ _ _) using (fields_appendDeleteKlong _ _ _)
  | whUse (mergesLe_emptyKeyNext _ _) using (fields_emptyKeyNext _ _)
  | whUse (mergesLe_segmentCount _ _) using (fields_segmentCount _ _)
  | whUse (mergesLe_unlinkLoop _ _ _) using (fields_unlinkLoop _ _ _)
  | whUse (mergesLe_setNode _ _ _) using (fields_setNode _ _ _)
  | whUse (mergesLe_findRoot) using (fields_findRoot))

end SIS.Tree
