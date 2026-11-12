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

theorem execW_heightMarked (p : Params) (tx : Tx) (i : Time) (v : View BVal)
    (bs : List Bool) (w : W) (h : execW p tx i v = .ok (bs,w)) :
    HeightMarkedPred p w.gh w.outside := by
  unfold execW runOps runOpsFrom at h
  cases hz : lastTop v with
  | none => simp [hz] at h
  | some z =>
    simp only [hz] at h
    cases ht : topOf p (rootless v) z with
    | error e => simp [ht] at h
    | ok top =>
      simp only [ht] at h
      have hr := boundsOK_ok p _ bs w h
      letI := heightMarkedFields
      exact fields_ops tx.ops {p := p, i := i, view := rootless v}
        {next := tx.base, top := top}
        (by change HeightMarkedPred p [] []; simp [HeightMarkedPred]) bs w hr

theorem execW_seenHeightBound_of_outside (p : Params) (tx : Tx) (i : Time) (v : View BVal)
    (bs : List Bool) (w : W) (cap : Nat) (h : execW p tx i v = .ok (bs,w))
    (hcap : p.H ≤ cap) (ho : ∀ q ∈ w.outside, q.2.2 ≤ cap) : SeenHeightBound cap w := by
  have hm := execW_heightMarked p tx i v bs w h
  intro x g height hx
  by_cases hb : height ≤ p.H
  · omega
  · exact ho (x,g,height) (hm x g height hx (by omega))

/-- Only the heights of exceptional creations need checking for TP32. -/
theorem execW_mergeOpBound_of_outsideHeight (p : Params) (tx : Tx) (i : Time) (v : View BVal)
    (bs : List Bool) (w : W) (h : execW p tx i v = .ok (bs,w))
    (ho : ∀ q ∈ w.outside, q.2.2 ≤ p.H+1) :
    w.merges ≤ deletesOf tx bs * (p.H+1) := by
  apply execW_mergeOpBound_of_transientHeight p tx i v bs w h
  exact execW_seenHeightBound_of_outside p tx i v bs w (p.H+1) h (by omega) ho

/-- When no node was created outside the bounds, the root level is excluded
and H itself suffices. -/
theorem execW_mergeBound_noOutside (p : Params) (tx : Tx) (i : Time) (v : View BVal)
    (bs : List Bool) (w : W) (h : execW p tx i v = .ok (bs,w)) (ho : w.outside = []) :
    w.merges ≤ deletesOf tx bs * p.H := by
  apply execW_mergeRootHeightBound_of_cache p tx i v bs w p.H h
  apply execW_seenHeightBound_of_outside p tx i v bs w p.H h (by omega)
  simp [ho]

end SIS.Tree
