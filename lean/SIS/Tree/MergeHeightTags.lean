import SIS.Tree.WriterFields

namespace SIS.Tree

open SIS SIS.Check

/-- A cached height above H has an entry in the writer's bounds check. -/
def HeightTagged (p : Params) (w : W) : Prop :=
  ∀ x g h, (x, g, h) ∈ w.gh → p.H < h → ∃ q ∈ w.outside, q.1 = x

def KeepsHeightTagged {α : Type} (f : M α) : Prop :=
  ∀ c w, HeightTagged c.p w → WriterWP f c w (fun _ v => HeightTagged c.p v)

theorem heightOf_le (p : Params) (level : Nat) : p.heightOf level ≤ p.H := by
  have h : (level - 1) % (p.H + 1) < p.H + 1 := Nat.mod_lt _ (by omega)
  unfold Params.heightOf
  omega

theorem heightTagged_getNode (x : NodeId) : KeepsHeightTagged (getNode x) := by
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
        rcases hd with ⟨rfl, rfl, rfl⟩ | hd
        · exact (Nat.not_lt_of_ge (heightOf_le c.p _) hh).elim
        · exact hw a b d hd hh
    · exact writerWP_throw _ _ _ _

theorem heightTagged_newKey (g h : Nat) (leaf : Bool) (ks : List Klong) :
    KeepsHeightTagged (newKey g h leaf ks) := by
  intro c w hw
  unfold newKey fresh
  wpSimplify
  split
  · wpSimplify
    intro a b d hd hh
    simp only [List.mem_cons, Prod.mk.injEq] at hd
    rcases hd with ⟨rfl, rfl, rfl⟩ | hd
    · exact ⟨(w.next, b, d), by simp, rfl⟩
    · obtain ⟨q, hq, heq⟩ := hw a b d hd hh
      exact ⟨q, List.mem_cons_of_mem _ hq, heq⟩
  · rename_i hflag
    wpSimplify
    have hbound : h ≤ c.p.H := by
      by_cases hh : c.p.H < h
      · simp [hh] at hflag
      · omega
    intro a b d hd hh
    simp only [List.mem_cons, Prod.mk.injEq] at hd
    rcases hd with ⟨rfl, rfl, rfl⟩ | hd
    · omega
    · exact hw a b d hd hh

@[instance_reducible]
def heightTaggedFields : WriterFieldsInvariant where
  pred := fun p gh outside =>
    ∀ x g h, (x, g, h) ∈ gh → p.H < h → ∃ q ∈ outside, q.1 = x
  load := heightTagged_getNode
  create := heightTagged_newKey

theorem heightTagged_ops (ops : List Tree.Op) : KeepsHeightTagged (ops.mapM putKv) := by
  letI := heightTaggedFields
  exact fields_ops ops

end SIS.Tree
