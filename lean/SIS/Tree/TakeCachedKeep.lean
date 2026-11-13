/-
A node the writer has cached stays cached (bergdb 024-12): the writer only
appends nodes to its cache or replaces them in place (`upsert`), so every writer
operation keeps every cached id cached. `cachedFromInvariant w0` is that fact
as a `WriterStateInvariant`, `writerWP_appendKlongs_cached` its use for a
cascade.
-/
import SIS.Tree.GetCommit

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- Every node cached in w0 is cached in w. -/
def CachedFrom (w0 : W) (_c : Ctx) (w : W) : Prop :=
  ∀ y, (w0.nodes.lookup y).isSome = true → (w.nodes.lookup y).isSome = true

theorem cachedFrom_mono (w0 : W) (c : Ctx) (w w' : W) (hw : CachedFrom w0 c w)
    (hn : ∀ y, (w.nodes.lookup y).isSome = true → (w'.nodes.lookup y).isSome = true) :
    CachedFrom w0 c w' :=
  fun y h => hn y (hw y h)

theorem cachedFrom_refl (w0 : W) (c : Ctx) : CachedFrom w0 c w0 := fun _ h => h

@[instance_reducible]
def cachedFromInvariant (w0 : W) : WriterStateInvariant where
  pred := CachedFrom w0
  load := by
    intro x c w hw
    unfold getNode
    simp only [writerWP_bind, writerWP_get]
    split
    · simpa only [writerWP_pure] using hw
    · simp only [writerWP_bind, writerWP_read]
      split
      · split
        · exact writerWP_throw _ _ _ _
        · simp only [writerWP_bind, writerWP_set, writerWP_pure]
          exact cachedFrom_mono w0 c w _ hw (fun y h => lookup_isSome_append _ _ y h)
      · exact writerWP_throw _ _ _ _
  store := by
    intro x n c w hw
    simp only [putNode, writerWP_modify]
    exact cachedFrom_mono w0 c w _ hw (fun y h => lookup_isSome_upsert _ x y n h)
  create := by
    intro g h leaf ks c w hw
    unfold newKey fresh
    wpSimplify
    split <;> wpSimplify <;>
    · exact cachedFrom_mono w0 c w _ hw (fun y h => lookup_isSome_append _ _ y h)
  value := by
    intro h c w hw
    unfold newValue fresh
    wpSimplify
    exact hw
  allocate := by
    intro c w hw
    unfold fresh
    wpSimplify
    exact hw
  trace := by
    intro s c w hw
    simp only [note, writerWP_modify]
    exact hw
  provenance := by
    intro x old c w hw
    unfold setMadeFor
    split
    · simp only [writerWP_modify]; exact hw
    · simpa only [writerWP_pure] using hw
  take := by
    intro x c w hw
    simp only [takenBack, writerWP_modify]
    exact hw
  clear := by
    intro c w hw
    simp only [pathClear, writerWP_modify]
    exact hw
  path := by
    intro cv x c w hw
    simp only [pathAdd, writerWP_modify]
    exact hw
  top := by
    intro x c w hw
    unfold newSuperRoot note fresh
    wpSimplify
    split
    · wpSimplify
      exact hw
    · wpSimplify
      exact hw
  mergeCounter := by intro c w hw; exact hw
  splitCounter := by intro c w hw; exact hw

/-- A cascade keeps every cached node cached. -/
theorem writerWP_appendKlongs_cached (depth : Nat) (x : NodeId) (ins : List (Nat × NodeId))
    (c : Ctx) (w : W) :
    WriterWP (appendKlongs depth x ins) c w (fun _ w' =>
      ∀ y, (w.nodes.lookup y).isSome = true → (w'.nodes.lookup y).isSome = true) :=
  @state_appendKlongs (cachedFromInvariant w) depth x ins c w (cachedFrom_refl w c)

end SIS.Tree
