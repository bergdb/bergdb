import SIS.Tree.MergeHeightExec

namespace SIS.Tree

open SIS SIS.Check

/-- Every cached height above H has its exact creation tag, including the
segment and height, in the final bounds check. -/
def HeightMarkedPred (p : Params) (gh outside : List (NodeId × Nat × Nat)) : Prop :=
  ∀ x g h, (x,g,h) ∈ gh → p.H < h → (x,g,h) ∈ outside

theorem heightMarked_getNode (x : NodeId) : KeepsFieldPred HeightMarkedPred (getNode x) := by
  intro c w hw
  unfold getNode
  simp only [writerWP_bind, writerWP_get]
  split
  · simpa only [writerWP_pure] using hw
  · simp only [writerWP_bind, writerWP_read]
    split
    · split
      · exact writerWP_throw _ _ _ _
      · simp only [writerWP_bind, writerWP_set, writerWP_pure]
        intro a b d hd hh
        simp only [List.mem_cons, Prod.mk.injEq] at hd
        rcases hd with ⟨rfl,rfl,rfl⟩ | hd
        · exact (Nat.not_lt_of_ge (heightOf_le c.p _) hh).elim
        · exact hw a b d hd hh
    · exact writerWP_throw _ _ _ _

theorem heightMarked_newKey (g h : Nat) (leaf : Bool) (ks : List Klong) :
    KeepsFieldPred HeightMarkedPred (newKey g h leaf ks) := by
  intro c w hw
  unfold newKey fresh
  wpSimplify
  split
  · wpSimplify
    intro a b d hd hh
    simp only [List.mem_cons, Prod.mk.injEq] at hd
    rcases hd with ⟨rfl,rfl,rfl⟩ | hd
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (hw a b d hd hh)
  · rename_i hflag
    wpSimplify
    have hbound : h ≤ c.p.H := by
      by_cases hh : c.p.H < h
      · simp [hh] at hflag
      · omega
    intro a b d hd hh
    simp only [List.mem_cons, Prod.mk.injEq] at hd
    rcases hd with ⟨rfl,rfl,rfl⟩ | hd
    · omega
    · exact hw a b d hd hh

@[instance_reducible]
def heightMarkedFields : WriterFieldsInvariant where
  pred := HeightMarkedPred
  load := heightMarked_getNode
  create := heightMarked_newKey

end SIS.Tree
