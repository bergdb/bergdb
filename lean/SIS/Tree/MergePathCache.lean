import SIS.Tree.MergeProtectedDelete

namespace SIS.Tree

open SIS SIS.Check

/-- Every node named by the access path is present in the writer cache. -/
def PathCached (w : W) : Prop :=
  ∀ e ∈ w.path, ∃ n, w.nodes.lookup e.2 = some n

/-- Only the node about to be read may still be absent from the cache. -/
def PathReady (x : NodeId) (w : W) : Prop :=
  ∀ e ∈ w.path, e.2 = x ∨ ∃ n, w.nodes.lookup e.2 = some n

theorem pathReady_of_cached (x : NodeId) (w : W) (hw : PathCached w) :
    PathReady x w := by
  intro e he
  exact Or.inr (hw e he)

theorem writerWP_getNode_path_cached (x : NodeId) (c : Ctx) (w : W)
    (hw : PathReady x w) :
    WriterWP (getNode x) c w (fun _ v => PathCached v) := by
  refine writerWP_mono (writerWP_getNode_cache x c w) ?_
  rintro n v ⟨hn,hprefix,hpath⟩
  intro e he
  rw [hpath] at he
  rcases hw e he with hx | hk
  · exact ⟨n,by simpa only [hx] using hn⟩
  · obtain ⟨old,hold⟩ := hk
    exact ⟨old,hprefix.lookup_eq_some hold⟩

theorem writerWP_pathAdd_ready (cv : Option Nat) (x : NodeId) (c : Ctx) (w : W)
    (hw : PathCached w) :
    WriterWP (pathAdd cv x) c w (fun _ v => PathReady x v) := by
  simp only [pathAdd,writerWP_modify]
  intro e he
  simp only [List.mem_append,List.mem_singleton] at he
  rcases he with he | rfl
  · exact Or.inr (hw e he)
  · exact Or.inl rfl

/-- Successful leaf descent has loaded every node on its access path,
including the final leaf. No ordering or committed-tree invariant is used. -/
theorem writerWP_descendLte_path_cached (cv fuel : Nat) (x : NodeId)
    (c : Ctx) (w : W) (hw : PathReady x w) :
    WriterWP (descendLte cv fuel x) c w (fun _ v => PathCached v) := by
  induction fuel generalizing x w with
  | zero => exact writerWP_throw _ _ _ _
  | succ fuel ih =>
    unfold descendLte
    simp only [writerWP_bind,writerWP_read]
    refine writerWP_mono (writerWP_getNode_path_cached x c w hw) ?_
    intro n v hv
    split
    · simpa only [writerWP_pure] using hv
    · split
      · exact writerWP_throw _ _ _ _
      · simp only [writerWP_bind]
        refine writerWP_mono (writerWP_pathAdd_ready _ _ c v hv) ?_
        intro _ u hu
        exact ih _ u hu

/-- A rebuilt segment-root path is ready for the next read: only the
returned root id may still be absent from the cache. -/
theorem writerWP_descendToSegmentRoot_ready (key : Key) (g : Nat) (c : Ctx) (w : W) :
    WriterWP (descendToSegmentRoot key g) c w (fun root v => PathReady root v) := by
  unfold descendToSegmentRoot pathClear findRoot pathAdd
  wpSimplify
  refine writerWP_foldlM_state _ _ _ _ _ (fun root v => PathReady root v) ?_ ?_
  · intro e he
    simp only [List.nil_append,List.mem_singleton] at he
    subst e
    exact Or.inl rfl
  · intro node cv v hv
    simp only [writerWP_bind]
    refine writerWP_mono (writerWP_descendLte_path_cached cv c.p.fuel node c v hv) ?_
    intro leaf u hu
    refine writerWP_mono (writerWP_getNode_path_cached leaf c u (pathReady_of_cached leaf u hu)) ?_
    intro n z hz
    split
    · exact writerWP_throw _ _ _ _
    · rename_i fd hfd
      simpa only [writerWP_bind,writerWP_pure,pathAdd] using
        writerWP_pathAdd_ready (some fd.c) fd.y c z hz

theorem writerWP_ghOf_path_cached (x : NodeId) (c : Ctx) (w : W)
    (hw : PathReady x w) :
    WriterWP (ghOf x) c w (fun _ v => PathCached v) := by
  unfold ghOf
  simp only [writerWP_bind]
  refine writerWP_mono (writerWP_getNode_path_cached x c w hw) ?_
  intro n v hv
  wpSimplify
  split
  · simpa only [writerWP_pure] using hv
  · exact writerWP_throw _ _ _ _

theorem writerWP_descendHeight_path_cached (cv h fuel : Nat) (x : NodeId)
    (c : Ctx) (w : W) (hw : PathReady x w) :
    WriterWP (descendHeight cv h fuel x) c w (fun _ v => PathCached v) := by
  induction fuel generalizing x w with
  | zero => exact writerWP_throw _ _ _ _
  | succ fuel ih =>
    unfold descendHeight
    simp only [writerWP_bind,writerWP_read]
    refine writerWP_mono (writerWP_ghOf_path_cached x c w hw) ?_
    intro gh v hv
    split
    · simpa only [writerWP_pure] using hv
    · simp only [writerWP_bind]
      refine writerWP_mono (writerWP_getNode_path_cached x c v (pathReady_of_cached x v hv)) ?_
      intro n u hu
      split
      · exact writerWP_throw _ _ _ _
      · split
        · exact writerWP_throw _ _ _ _
        · simp only [writerWP_bind]
          refine writerWP_mono (writerWP_pathAdd_ready _ _ c u hu) ?_
          intro _ z hz
          exact ih _ z hz

/-- The merge loop's rebuilt access path is fully cached on every
successful descent to height, without any sortedness or history premise. -/
theorem writerWP_descendToHeight_path_cached (key : Key) (g h : Nat) (c : Ctx) (w : W) :
    WriterWP (descendToHeight key g h) c w (fun _ v => PathCached v) := by
  unfold descendToHeight
  simp only [writerWP_bind,writerWP_read]
  refine writerWP_mono (writerWP_descendToSegmentRoot_ready key g c w) ?_
  intro root v hv
  split
  · exact writerWP_throw _ _ _ _
  · simp only [writerWP_bind]
    refine writerWP_mono (writerWP_descendHeight_path_cached _ h c.p.fuel root c v hv) ?_
    intro _ u hu
    simpa only [pathSize,writerWP_bind,writerWP_get,writerWP_pure] using hu

end SIS.Tree
