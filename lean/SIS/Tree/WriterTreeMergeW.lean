/-
The writer's code of the merge (bergdb 024-22, `OpTreeOK`): `mergeParent` with
room for its klongs and no compaction writes `mergeParentNode` at the parent
and changes nothing else (`writerWP_mergeParent_room`).
-/
import SIS.Tree.WriterTreeMergeLive

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

theorem writerWP_ite_true {α : Type} (b : Prop) [Decidable b] (h : b) (x y : M α) (c : Ctx) (w : W)
    (post : α → W → Prop) (hx : WriterWP x c w post) : WriterWP (if b then x else y) c w post := by
  simp only [h, ↓reduceIte]; exact hx

theorem writerWP_ite_false {α : Type} (b : Prop) [Decidable b] (h : ¬ b) (x y : M α) (c : Ctx)
    (w : W) (post : α → W → Prop) (hy : WriterWP y c w post) :
    WriterWP (if b then x else y) c w post := by
  simp only [h, ↓reduceIte]; exact hy

theorem need_le_four (b1 b2 b3 b4 : Bool) :
    (((if b1 = true then 1 else 0) + (if b2 = true then 0 else 1)) +
      (if b3 = true then 0 else 1)) + (if b4 = true then 0 else 1) ≤ 4 := by
  cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> simp

/-- `mergeParent` with room: the parent gets `mergeParentNode`, nothing else
changes but the trail. -/
theorem writerWP_mergeParent_room (p : NodeId) (pn : KNode) (depth il cL : Nat) (m1 : NodeId)
    (ir cR : Nat) (m2 : Option (NodeId × Nat)) (c : Ctx) (w : W)
    (hlk : w.nodes.lookup p = some pn) (hroom : pn.size + 4 ≤ c.p.M)
    (hdead : deadOver c.p (mergeParentNode pn c.i il cL m1 ir cR m2) = false) :
    WriterWP (mergeParent p depth il cL m1 ir cR m2) c w (fun _ w' =>
      w'.nodes = upsert w.nodes p (mergeParentNode pn c.i il cL m1 ir cR m2) ∧
      w'.taken = w.taken ∧ w'.top = w.top ∧ w'.next = w.next ∧ w'.vals = w.vals ∧
      w'.path = w.path ∧ w'.gh = w.gh ∧ w'.madeFor = w.madeFor) := by
  unfold mergeParent
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known p pn c w hlk]
  apply writerWP_ite_true _ (Nat.le_trans (Nat.add_le_add_left (need_le_four _ _ _ _) _) hroom)
  apply writerWP_ite_false _ (fun hd => absurd (hd.symm.trans hdead) (by decide))
  simp only [note, putNode, writerWP_bind, writerWP_modify]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> first | rfl | trivial

/-- `newKey` makes the node at the next id. -/
theorem writerWP_newKey_frame (g h : Nat) (leaf : Bool) (ks : List Klong) (c : Ctx) (w : W) :
    WriterWP (newKey g h leaf ks) c w (fun x w' => x = w.next ∧
      w'.nodes = w.nodes ++ [(w.next, ⟨leaf, ks⟩)] ∧ w'.taken = w.taken ∧ w'.top = w.top ∧
      w'.next = w.next + 2 ∧ w'.vals = w.vals ∧ w'.path = w.path ∧ w'.madeFor = w.madeFor) := by
  unfold newKey fresh
  simp only [writerWP_bind, writerWP_read, writerWP_get, writerWP_set]
  split <;>
  · simp only [writerWP_bind, writerWP_modify, writerWP_pure]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> first | rfl | trivial

theorem writerWP_setMadeFor_frame (m : NodeId) (o : Option NodeId) (c : Ctx) (w : W) :
    WriterWP (setMadeFor m o) c w (fun _ w' => w'.nodes = w.nodes ∧ w'.taken = w.taken ∧
      w'.top = w.top ∧ w'.next = w.next ∧ w'.vals = w.vals ∧ w'.path = w.path) := by
  unfold setMadeFor
  split
  · simp only [writerWP_modify]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> first | rfl | trivial
  · simp only [writerWP_pure]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> first | rfl | trivial

/-- `getNode` changes at most the lookup of the node it reads. -/
theorem writerWP_getNode_frame (x : NodeId) (c : Ctx) (w : W) :
    WriterWP (getNode x) c w (fun _ w' => w'.taken = w.taken ∧ w'.top = w.top ∧
      w'.next = w.next ∧ w'.vals = w.vals ∧ w'.path = w.path ∧ w'.madeFor = w.madeFor ∧
      ∀ y, y ≠ x → w'.nodes.lookup y = w.nodes.lookup y) := by
  unfold getNode
  simp only [writerWP_bind, writerWP_get]
  split
  · simp only [writerWP_pure]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun _ _ => ?_⟩ <;> first | rfl | trivial
  · simp only [writerWP_bind, writerWP_read]
    split
    · split
      · exact writerWP_throw _ _ _ _
      · simp only [writerWP_bind, writerWP_set, writerWP_pure]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun y hy => ?_⟩
        any_goals first | rfl | trivial
        simp only [List.lookup_append]
        cases h : w.nodes.lookup y with
        | some _ => rfl
        | none =>
          show (none : Option KNode).or ([(x, _)].lookup y) = none
          rw [lookup_cons_ne _ _ _ _ hy]; rfl
    · exact writerWP_throw _ _ _ _

/-- `unlink` changes at most the lookup of its node. -/
theorem writerWP_unlink_frame (o : NodeId) (c : Ctx) (w : W) :
    WriterWP (unlink o) c w (fun _ w' => w'.taken = w.taken ∧ w'.top = w.top ∧
      w'.next = w.next ∧ ∀ y, y ≠ o → w'.nodes.lookup y = w.nodes.lookup y) := by
  unfold unlink
  simp only [writerWP_bind, writerWP_read]
  refine writerWP_mono (writerWP_getNode_frame o c w) ?_
  intro n w1 ⟨h1t, h1top, h1n, _, _, _, h1l⟩
  split
  · simp only [putNode, writerWP_modify]
    refine ⟨h1t, h1top, h1n, fun y hy => ?_⟩
    simp only [lookup_upsert, hy, ↓reduceIte]
    exact h1l y hy
  · simp only [writerWP_pure]
    exact ⟨h1t, h1top, h1n, h1l⟩

/-- The merge's last loop when it made neither node: each is unlinked, and
nothing else changes but their lookups. -/
theorem writerWP_mergeCleanup_unmade (parent m1 : NodeId) (c : Ctx) :
    ∀ (xs : List (NodeId × Bool)) (w : W), (∀ q ∈ xs, q.2 = false) →
    WriterWP (forIn xs PUnit.unit (fun q _ => do
      if q.2 then
        retarget parent q.1 m1
        takenBack q.1
        note "merge.takeback"
      else unlink q.1
      pure (ForInStep.yield PUnit.unit))) c w (fun _ w' => w'.taken = w.taken ∧ w'.top = w.top ∧
      w'.next = w.next ∧ ∀ y, (∀ q ∈ xs, y ≠ q.1) → w'.nodes.lookup y = w.nodes.lookup y) := by
  intro xs
  induction xs with
  | nil =>
    intro w _
    simp only [List.forIn_nil, writerWP_pure]
    refine ⟨?_, ?_, ?_, fun _ _ => ?_⟩ <;> first | rfl | trivial
  | cons q qs ih =>
    intro w hq
    rw [List.forIn_cons]
    have hq0 : q.2 = false := hq q List.mem_cons_self
    simp only [writerWP_bind, hq0, Bool.false_eq_true, ↓reduceIte]
    refine writerWP_mono (writerWP_unlink_frame q.1 c w) ?_
    intro _ w1 ⟨h1t, h1top, h1n, h1l⟩
    simp only [writerWP_pure]
    refine writerWP_mono (ih w1 (fun q' hq' => hq q' (List.mem_cons_of_mem _ hq'))) ?_
    intro _ w2 ⟨h2t, h2top, h2n, h2l⟩
    refine ⟨h2t.trans h1t, h2top.trans h1top, h2n.trans h1n, fun y hy => ?_⟩
    rw [h2l y (fun q' hq' => hy q' (List.mem_cons_of_mem _ hq')),
      h1l y (hy q List.mem_cons_self)]

end SIS.Tree
