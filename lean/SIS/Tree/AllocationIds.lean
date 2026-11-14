import SIS.Tree.WriterStateInvariant
import SIS.Tree.SearchFold

namespace SIS.Tree

open SIS SIS.Check

/-- Every allocation has a distinct id in the transaction's fresh interval. -/
def AllocatedIds (base : NodeId) (w : W) : Prop :=
  base ≤ w.next ∧ (w.made.map (·.id)).Nodup ∧
    ∀ n ∈ w.made, base ≤ n.id ∧ n.id < w.next

theorem allocatedIds_weaken (base : NodeId) (w v : W) (hw : AllocatedIds base w)
    (hm : v.made = w.made) (hn : w.next ≤ v.next) : AllocatedIds base v := by
  refine ⟨Nat.le_trans hw.1 hn,?_,?_⟩
  · simpa only [hm] using hw.2.1
  · intro n hmem
    rw [hm] at hmem
    obtain ⟨hl,hu⟩ := hw.2.2 n hmem
    exact ⟨hl,Nat.lt_of_lt_of_le hu hn⟩

theorem allocatedIds_append (base : NodeId) (w : W) (level : Nat) (isData : Bool)
    (hw : AllocatedIds base w) :
    AllocatedIds base {w with
      next := w.next+2
      made := w.made ++ [⟨w.next,level,isData⟩]} := by
  dsimp only [AllocatedIds]
  refine ⟨by have := hw.1; omega,?_,?_⟩
  · simp only [List.map_append,List.map_cons,List.map_nil]
    apply List.nodup_append.mpr
    refine ⟨hw.2.1,by simp,?_⟩
    intro a ha b hb hab
    have hb' : b = w.next := by simpa only [List.mem_singleton] using hb
    obtain ⟨n,hn,hna⟩ := List.mem_map.mp ha
    have hu := (hw.2.2 n hn).2
    omega
  · intro n hn
    simp only [List.mem_append,List.mem_singleton] at hn
    rcases hn with hn | rfl
    · obtain ⟨hl,hu⟩ := hw.2.2 n hn
      exact ⟨hl,by omega⟩
    · exact ⟨hw.1,by dsimp only; omega⟩

@[instance_reducible]
def allocatedIdsInvariant (base : NodeId) : WriterStateInvariant where
  pred := fun _ w => AllocatedIds base w
  load := by
    intro x c w hw
    unfold getNode
    simp only [writerWP_bind,writerWP_get]
    split
    · simpa only [writerWP_pure] using hw
    · simp only [writerWP_bind,writerWP_read]
      split
      · split
        · exact writerWP_throw _ _ _ _
        · simp only [writerWP_bind,writerWP_set,writerWP_pure]
          exact hw
      · exact writerWP_throw _ _ _ _
  store := by
    intro x n c w hw
    simp only [putNode,writerWP_modify]
    exact hw
  create := by
    intro g h leaf ks c w hw
    have ha := allocatedIds_append base w (c.p.keyLevel g h) false hw
    unfold newKey fresh
    wpSimplify
    split <;> wpSimplify <;> exact ha
  value := by
    intro h c w hw
    have ha := allocatedIds_append base w 0 true hw
    unfold newValue fresh
    wpSimplify
    exact ha
  allocate := by
    intro c w hw
    unfold fresh
    wpSimplify
    exact allocatedIds_weaken base w _ hw rfl (by dsimp only; omega)
  trace := by
    intro s c w hw
    simp only [note,writerWP_modify]
    exact hw
  provenance := by
    intro x old c w hw
    unfold setMadeFor
    split
    · simp only [writerWP_modify]; exact hw
    · simpa only [writerWP_pure] using hw
  take := by
    intro x c w hw
    simp only [takenBack,writerWP_modify]
    exact hw
  clear := by
    intro c w hw
    simp only [pathClear,writerWP_modify]
    exact hw
  path := by
    intro cv x c w hw
    simp only [pathAdd,writerWP_modify]
    exact hw
  top := by
    intro x c w hw
    unfold newSuperRoot note fresh
    wpSimplify
    split
    · wpSimplify; exact hw
    · wpSimplify
      exact allocatedIds_append base w
        (c.p.topLevel (if w.top.ord == 0 then 1 else w.top.ord+1)) false hw
  mergeCounter := by intro c w hw; exact hw
  splitCounter := by intro c w hw; exact hw

/-- The complete writer keeps allocation ids fresh and pairwise distinct.
No assumptions on the transaction, parameters, input view or history are
needed for this successful-result property. -/
theorem execW_allocatedIds (p : Params) (tx : Tx) (i : Time) (v : View BVal)
    (bs : List Bool) (w : W) (he : execW p tx i v = .ok (bs,w)) : AllocatedIds tx.base w := by
  unfold execW runOps runOpsFrom at he
  cases hz : lastTop v with
  | none => simp [hz] at he
  | some z =>
    simp only [hz] at he
    cases ht : topOf p (rootless v) z with
    | error e => simp [ht] at he
    | ok top =>
      simp only [ht] at he
      have hr := boundsOK_ok p _ bs w he
      letI := allocatedIdsInvariant tx.base
      exact state_ops tx.ops {p := p,i := i,view := rootless v}
        {next := tx.base,top := top} (by
          change AllocatedIds tx.base _
          simp [AllocatedIds]) bs w hr

end SIS.Tree
