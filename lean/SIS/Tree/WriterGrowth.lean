import SIS.Tree.WriterFields

namespace SIS.Tree

open SIS SIS.Check

/-- The height cache and the list checked by boundsOK only grow. -/
def FieldsGrow {α : Type} (f : M α) : Prop :=
  ∀ c w, WriterWP f c w (fun _ v => w.gh.Sublist v.gh ∧ w.outside.Sublist v.outside)

@[instance_reducible]
def growingFields (gh outside : List (NodeId × Nat × Nat)) : WriterFieldsInvariant where
  pred := fun _ ns os => gh.Sublist ns ∧ outside.Sublist os
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
          exact ⟨hw.1.cons _, hw.2⟩
      · exact writerWP_throw _ _ _ _
  create := by
    intro g h leaf ks c w hw
    unfold newKey fresh
    wpSimplify
    split
    · wpSimplify
      exact ⟨hw.1.cons _, hw.2.cons _⟩
    · wpSimplify
      exact ⟨hw.1.cons _, hw.2⟩

theorem fieldsGrow_of_invariant {α : Type} {f : M α}
    (hf : ∀ inv : WriterFieldsInvariant, @KeepsFields α inv f) : FieldsGrow f := by
  intro c w
  exact hf (growingFields w.gh w.outside) c w ⟨.refl _, .refl _⟩

macro "growthFrom " h:term : tactic => `(tactic| (
  apply fieldsGrow_of_invariant
  intro inv
  letI := inv
  exact $h))

theorem fieldsGrow_getNode (x : NodeId) : FieldsGrow (getNode x) := by
  growthFrom (fields_getNode x)

theorem fieldsGrow_ghOf (x : NodeId) : FieldsGrow (ghOf x) := by
  growthFrom (fields_ghOf x)

theorem fieldsGrow_descendLte (cv fuel : Nat) (x : NodeId) : FieldsGrow (descendLte cv fuel x) := by
  growthFrom (fields_descendLte cv fuel x)

theorem fieldsGrow_descendHeight (cv h fuel : Nat) (x : NodeId) : FieldsGrow (descendHeight cv h fuel x) := by
  growthFrom (fields_descendHeight cv h fuel x)

theorem fieldsGrow_descendToSegmentRoot (key : Key) (g : Nat) : FieldsGrow (descendToSegmentRoot key g) := by
  growthFrom (fields_descendToSegmentRoot key g)

theorem fieldsGrow_descendToHeight (key : Key) (g h : Nat) : FieldsGrow (descendToHeight key g h) := by
  growthFrom (fields_descendToHeight key g h)

theorem fieldsGrow_merge (x : NodeId) (d : Nat) : FieldsGrow (merge x d) := by
  growthFrom (fields_merge x d)

theorem fieldsGrow_mergeUp (key : Key) (g fuel h : Nat) (merged : Bool) :
    FieldsGrow (mergeUp key g fuel h merged) := by
  growthFrom (fields_mergeUp key g fuel h merged)

theorem fieldsGrow_collapseRoot (key : Key) (g fuel : Nat) :
    FieldsGrow (collapseRoot key g fuel) := by
  growthFrom (fields_collapseRoot key g fuel)

theorem fieldsGrow_deleteUpward (leaf : NodeId) (depth cv : Nat) (key : Key) :
    FieldsGrow (deleteUpward leaf depth cv key) := by
  growthFrom (fields_deleteUpward leaf depth cv key)

theorem fieldsGrow_setValue (root : NodeId) (cv : Nat) (key : Key) (value : Option Nat) :
    FieldsGrow (setValue root cv key value) := by
  growthFrom (fields_setValue root cv key value)

theorem fieldsGrow_putSegs (key : Key) (value : Option Nat) (segs : List Nat) (root : NodeId) :
    FieldsGrow (putSegs key value segs root) := by
  growthFrom (fields_putSegs key value segs root)

theorem fieldsGrow_putKv (op : Tree.Op) : FieldsGrow (putKv op) := by
  growthFrom (fields_putKv op)

theorem fieldsGrow_ops (ops : List Tree.Op) : FieldsGrow (ops.mapM putKv) := by
  growthFrom (fields_ops ops)

end SIS.Tree
