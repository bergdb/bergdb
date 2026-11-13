/-
The tree model (bergdb 024-12, TP7): what the writer's lists of made nodes
say of each other (`Ledger`), kept by every step of the writer: a key node
made within the level bounds is in the overlay; a value made is in the list
of made nodes as a data node; the transaction's own top node is in it with a
level above the key nodes'. With `AllocatedIds` (no id made twice) the
entries that `changesOf` gives a key node are those of its overlay node
alone (SIS/Tree/ApplyBridge.lean).
-/
import SIS.Tree.WriterKinds

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- The writer's lists agree: made key nodes are in the overlay, values are
made as data nodes, the new top node is made above the key levels. -/
def Ledger (c : Ctx) (w : W) : Prop :=
  (∀ nn ∈ w.made, nn.isData = false → nn.level ≤ c.p.keyMax → ∃ n, (nn.id, n) ∈ w.nodes) ∧
  (∀ q ∈ w.vals, (⟨q.1, 0, true⟩ : NewNode) ∈ w.made) ∧
  (w.newTop = true → ∃ lvl, c.p.keyMax < lvl ∧ (⟨w.top.id, lvl, false⟩ : NewNode) ∈ w.made)

theorem upsert_keeps_id (ns : List (NodeId × KNode)) (x y : NodeId) (n m : KNode)
    (h : (y, m) ∈ ns) : ∃ m', (y, m') ∈ upsert ns x n := by
  unfold upsert
  split
  · by_cases hy : y = x
    · subst hy
      exact ⟨n, List.mem_map.mpr ⟨(y, m), h, by simp⟩⟩
    · exact ⟨m, List.mem_map.mpr ⟨(y, m), h, by simp [hy]⟩⟩
  · exact ⟨m, List.mem_append_left _ h⟩

@[instance_reducible]
def ledgerInvariant : WriterStateInvariant where
  pred := Ledger
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
          refine ⟨?_, hw.2.1, hw.2.2⟩
          intro nn hn hd hl
          obtain ⟨n, hm⟩ := hw.1 nn hn hd hl
          exact ⟨n, List.mem_append_left _ hm⟩
      · exact writerWP_throw _ _ _ _
  store := by
    intro x n c w hw
    simp only [putNode,writerWP_modify]
    refine ⟨?_, hw.2.1, hw.2.2⟩
    intro nn hn hd hl
    obtain ⟨m, hm⟩ := hw.1 nn hn hd hl
    exact upsert_keeps_id w.nodes x nn.id n m hm
  create := by
    intro g h leaf ks c w hw
    unfold newKey fresh
    wpSimplify
    split <;> wpSimplify
    all_goals
      refine ⟨?_, ?_, ?_⟩
      · intro nn hn hd hl
        simp only [List.mem_append,List.mem_singleton] at hn
        rcases hn with hn | rfl
        · obtain ⟨m, hm⟩ := hw.1 nn hn hd hl
          exact ⟨m, List.mem_append_left _ hm⟩
        · exact ⟨⟨leaf, ks⟩, List.mem_append_right _ (List.mem_singleton.mpr rfl)⟩
      · intro q hq
        exact List.mem_append_left _ (hw.2.1 q hq)
      · intro ht
        obtain ⟨lvl, hl, hm⟩ := hw.2.2 ht
        exact ⟨lvl, hl, List.mem_append_left _ hm⟩
  value := by
    intro h c w hw
    unfold newValue fresh
    wpSimplify
    refine ⟨?_, ?_, ?_⟩
    · intro nn hn hd hl
      simp only [List.mem_append,List.mem_singleton] at hn
      rcases hn with hn | rfl
      · exact hw.1 nn hn hd hl
      · cases hd
    · intro q hq
      simp only [List.mem_append,List.mem_singleton] at hq
      rcases hq with hq | rfl
      · exact List.mem_append_left _ (hw.2.1 q hq)
      · exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
    · intro ht
      obtain ⟨lvl, hl, hm⟩ := hw.2.2 ht
      exact ⟨lvl, hl, List.mem_append_left _ hm⟩
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
    · wpSimplify
      refine ⟨?_, ?_, ?_⟩
      · intro nn hn hd hl
        simp only [List.mem_append,List.mem_singleton] at hn
        rcases hn with hn | rfl
        · exact hw.1 nn hn hd hl
        · simp only [Params.topLevel] at hl
          omega
      · intro q hq
        exact List.mem_append_left _ (hw.2.1 q hq)
      · intro _
        refine ⟨c.p.topLevel (if w.top.ord == 0 then 1 else w.top.ord + 1), ?_,
          List.mem_append_right _ (List.mem_singleton.mpr rfl)⟩
        simp only [Params.topLevel]
        omega
  mergeCounter := by intro c w hw; exact hw
  splitCounter := by intro c w hw; exact hw

/-- The writer's lists agree at the end of a successful transaction. -/
theorem execW_ledger (p : Params) (tx : Tx) (i : Time) (v : View BVal)
    (bs : List Bool) (w : W) (he : execW p tx i v = .ok (bs,w)) :
    Ledger {p := p,i := i,view := rootless v} w := by
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
      letI := ledgerInvariant
      exact state_ops tx.ops {p := p,i := i,view := rootless v}
        {next := tx.base,top := top} (by
          change Ledger _ _
          simp [Ledger]) bs w hr

end SIS.Tree
