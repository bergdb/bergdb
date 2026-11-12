import SIS.Tree.AllocationIds

namespace SIS.Tree

open SIS SIS.Check

/-- A nondata allocation above the key levels is either marked outside the
bounds, or is the transaction's current top node. -/
def MadeKinds (c : Ctx) (w : W) : Prop :=
  ∀ n ∈ w.made, n.isData = false → c.p.keyMax < n.level →
    (∃ q ∈ w.outside, q.1 = n.id) ∨
      (n.id = w.top.id ∧ w.newTop = true ∧ w.top.time = c.i)

theorem keyLevel_le_keyMax (p : Params) (g h : Nat) (hh : h ≤ p.H) :
    p.keyLevel g h ≤ p.keyMax := by
  unfold Params.keyLevel Params.keyMax
  have hg : p.G-g ≤ p.G := Nat.sub_le _ _
  have hm := Nat.mul_le_mul_right (p.H+1) hg
  omega

theorem madeKinds_newKey (c : Ctx) (w : W) (g h : Nat) (hw : MadeKinds c w) :
    MadeKinds c {w with
      made := w.made ++ [⟨w.next,c.p.keyLevel g h,false⟩]
      outside := if c.p.G < g || c.p.H < h then (w.next,g,h)::w.outside else w.outside} := by
  intro n hn hd hl
  simp only [List.mem_append,List.mem_singleton] at hn
  rcases hn with hn | rfl
  · rcases hw n hn hd hl with ho | ht
    · left
      obtain ⟨q,hq,he⟩ := ho
      refine ⟨q,?_,he⟩
      split <;> simp [hq]
    · exact Or.inr ht
  · left
    have hh : c.p.H < h := by
      have hc := keyLevel_le_keyMax c.p g h
      dsimp only at hl
      omega
    refine ⟨(w.next,g,h),?_,rfl⟩
    simp [hh]

@[instance_reducible]
def madeKindsInvariant : WriterStateInvariant where
  pred := MadeKinds
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
    have hk := madeKinds_newKey c w g h hw
    unfold newKey fresh
    wpSimplify
    split <;> wpSimplify
    · rename_i hflag
      simpa only [MadeKinds,hflag,Bool.false_eq_true,↓reduceIte] using hk
    · rename_i hflag
      simpa only [MadeKinds,hflag,Bool.false_eq_true,↓reduceIte] using hk
  value := by
    intro h c w hw
    unfold newValue fresh
    wpSimplify
    intro n hn hd hl
    simp only [List.mem_append,List.mem_singleton] at hn
    rcases hn with hn | rfl
    · exact hw n hn hd hl
    · cases hd
  allocate := by
    intro c w hw
    unfold fresh
    wpSimplify
    exact hw
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
    · wpSimplify
      exact hw
    · rename_i htime
      wpSimplify
      intro n hn hd hl
      simp only [List.mem_append,List.mem_singleton] at hn
      rcases hn with hn | rfl
      · rcases hw n hn hd hl with ho | ht
        · exact Or.inl ho
        · have he : c.i = w.top.time := ht.2.2.symm
          simp [he] at htime
      · exact Or.inr ⟨rfl,rfl,rfl⟩
  mergeCounter := by intro c w hw; exact hw
  splitCounter := by intro c w hw; exact hw

/-- The complete writer separates high key allocations from top nodes. -/
theorem execW_madeKinds (p : Params) (tx : Tx) (i : Time) (v : View BVal)
    (bs : List Bool) (w : W) (he : execW p tx i v = .ok (bs,w)) :
    MadeKinds {p := p,i := i,view := rootless v} w := by
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
      letI := madeKindsInvariant
      exact state_ops tx.ops {p := p,i := i,view := rootless v}
        {next := tx.base,top := top} (by
          change MadeKinds _ _
          simp [MadeKinds]) bs w hr

theorem changesOf_new_mem (i : Time) (w : W) (n : NewNode)
    (hn : n ∈ (changesOf i w).new) : n ∈ w.made ∧ w.taken.contains n.id = false := by
  change n ∈ (w.made.filter (fun n => !w.taken.contains n.id)).mergeSort _ at hn
  have hf := List.mem_filter.mp ((List.mergeSort_perm _ _).mem_iff.mp hn)
  exact ⟨hf.1,by simpa using hf.2⟩

/-- Every exported nondata node above the key levels is the newly made top.
The final bounds check removes all other high allocations. -/
theorem execW_high_new_is_top (p : Params) (tx : Tx) (i : Time) (v : View BVal)
    (bs : List Bool) (w : W) (he : execW p tx i v = .ok (bs,w))
    (n : NewNode) (hn : n ∈ (changesOf i w).new)
    (hd : n.isData = false) (hl : p.keyMax < n.level) :
    n.id = w.top.id ∧ w.newTop = true ∧ w.top.time = i := by
  obtain ⟨hm,hnot⟩ := changesOf_new_mem i w n hn
  rcases execW_madeKinds p tx i v bs w he n hm hd hl with ho | ht
  · obtain ⟨q,hq,heq⟩ := ho
    have hb := he
    unfold execW runOps runOpsFrom at hb
    cases hz : lastTop v with
    | none => simp [hz] at hb
    | some z =>
      simp only [hz] at hb
      cases hz' : topOf p (rootless v) z with
      | error e => simp [hz'] at hb
      | ok top =>
        simp only [hz'] at hb
        have ht := boundsOK_outside_taken p _ bs w hb q hq
        rw [heq,hnot] at ht
        cases ht
  · exact ht

end SIS.Tree
