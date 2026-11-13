/-
The writer's merge keeps every reading (bergdb 024-12, TP10's `OpGetOK`;
024-22): the merge's last part, `mergeTail`, from the siblings to the parent
with room, keeps `wGet` of every key (`writerWP_mergeTail_get`), the
siblings' compare values in their ranges (putinv's `RangeOrder`).
-/
import SIS.Tree.WriterGetMergeIdx
import SIS.Tree.WriterTreeMergeOp

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

theorem writerWP_unlink_frameV (o : NodeId) (c : Ctx) (w : W) :
    WriterWP (unlink o) c w (fun _ w' => w'.taken = w.taken ∧ w'.top = w.top ∧
      w'.next = w.next ∧ w'.vals = w.vals ∧ ∀ y, y ≠ o → w'.nodes.lookup y = w.nodes.lookup y) := by
  unfold unlink
  simp only [writerWP_bind, writerWP_read]
  refine writerWP_mono (writerWP_getNode_frame o c w) ?_
  intro n w1 ⟨h1t, h1top, h1n, h1v, _, _, h1l⟩
  split
  · simp only [putNode, writerWP_modify]
    refine ⟨h1t, h1top, h1n, h1v, fun y hy => ?_⟩
    simp only [lookup_upsert, hy, ↓reduceIte]
    exact h1l y hy
  · simp only [writerWP_pure]
    exact ⟨h1t, h1top, h1n, h1v, h1l⟩

theorem writerWP_mergeCleanup_unmadeV (A : NodeId × Bool → M (ForInStep PUnit)) (c : Ctx) :
    ∀ (xs : List (NodeId × Bool)) (w : W), (∀ q ∈ xs, q.2 = false) →
    WriterWP (forIn xs PUnit.unit (fun q _ => if q.2 = true then A q else do
      unlink q.1
      pure (ForInStep.yield PUnit.unit))) c w (fun _ w' => w'.taken = w.taken ∧ w'.top = w.top ∧
      w'.next = w.next ∧ w'.vals = w.vals ∧
      ∀ y, (∀ q ∈ xs, y ≠ q.1) → w'.nodes.lookup y = w.nodes.lookup y) := by
  intro xs
  induction xs with
  | nil =>
    intro w _
    simp only [List.forIn_nil, writerWP_pure]
    refine ⟨?_, ?_, ?_, ?_, fun _ _ => ?_⟩ <;> first | rfl | trivial
  | cons q qs ih =>
    intro w hq
    rw [List.forIn_cons]
    have hq0 : q.2 = false := hq q List.mem_cons_self
    simp only [writerWP_bind, hq0, Bool.false_eq_true, ↓reduceIte]
    refine writerWP_mono (writerWP_unlink_frameV q.1 c w) ?_
    intro _ w1 ⟨h1t, h1top, h1n, h1v, h1l⟩
    simp only [writerWP_pure]
    refine writerWP_mono (ih w1 (fun q' hq' => hq q' (List.mem_cons_of_mem _ hq'))) ?_
    intro _ w2 ⟨h2t, h2top, h2n, h2v, h2l⟩
    refine ⟨h2t.trans h1t, h2top.trans h1top, h2n.trans h1n, h2v.trans h1v, fun y hy => ?_⟩
    rw [h2l y (fun q' hq' => hy q' (List.mem_cons_of_mem _ hq')),
      h1l y (hy q List.mem_cons_self)]

theorem wValue_congr' (base : View BVal) (v w : W) (ht : v.taken = w.taken) (hv : v.vals = w.vals) :
    wValue base v = wValue base w := by
  funext y; simp only [wValue, ht, hv]

/-- A node's links from its live klongs' lookups. -/
theorem mrg_liveAt_iff_lookup (m : KNode) (t : Time) (ht : ∀ s, Klong.time s ∈ m.ks → s ≤ t)
    (f : Nat → Option NodeId) (h : ∀ cc, m.live.lookup cc = f cc) :
    ∀ cc z, (cc, z) ∈ m.liveAt t ↔ f cc = some z := by
  intro cc z
  rw [KNode.liveAt_of_times m t ht, mem_iff_lookup _ (KNode.live_keys_nodup m), h cc]

/-- The halves of a merge into two nodes: the first ceil(n/2) klongs, and the
rest with its first compare value g, renamed in an inner node. -/
theorem mrg_splitMerged_two (inner : Bool) (cap : Nat) (hcap : 1 ≤ cap) (e E1 E2 : List (Nat × NodeId))
    (g : Nat) (h : splitMerged inner cap e = (E1, some (E2, g))) :
    ∃ yg, E1 = e.take ((e.length + 1) / 2) ∧
      (e.drop ((e.length + 1) / 2)).head? = some (g, yg) ∧
      E2 = (if inner then renameHead 0 (e.drop ((e.length + 1) / 2)) else e.drop ((e.length + 1) / 2)) := by
  unfold splitMerged at h
  split at h
  · cases h
  · rename_i hlen
    simp only [Prod.mk.injEq, Option.some.injEq] at h
    obtain ⟨h1, h2, h3⟩ := h
    cases hd : e.drop ((e.length + 1) / 2) with
    | nil =>
      exfalso
      have := congrArg List.length hd
      simp only [List.length_drop, List.length_nil] at this
      omega
    | cons a rest =>
      obtain ⟨a1, a2⟩ := a
      rw [hd] at h2 h3
      simp only [List.head?_cons, Option.map_some, Option.getD_some] at h3
      refine ⟨a2, h1.symm, ?_, ?_⟩
      · simp [h3]
      · exact h2.symm

theorem mrg_repoint_leaf (n : KNode) (i : Nat) (y : NodeId) : (n.repoint i y).leaf = n.leaf := by
  unfold KNode.repoint; split <;> rfl

theorem mrg_mergeParentNode_leaf (pn : KNode) (tt : Time) (il cL : Nat) (m1 : NodeId) (ir cR : Nat)
    (m2 : Option (NodeId × Nat)) : (mergeParentNode pn tt il cL m1 ir cR m2).leaf = pn.leaf := by
  have h1 : ∀ (b : Bool) (k : Klong) (n : KNode),
      (if b = true then n.setAt (n.size - 1) k else n.add tt k).leaf = n.leaf := by
    intro b k n; cases b <;> simp [KNode.add_leaf, KNode.setAt_leaf]
  have h2 : ∀ (b : Bool) (n : KNode) (i : Nat) (y : NodeId) (k : Klong),
      (if b = true then n.repoint i y else n.add tt k).leaf = n.leaf := by
    intro b n i y k; cases b <;> simp [KNode.add_leaf, mrg_repoint_leaf]
  rw [mergeParentNode_eq]
  unfold mpNode
  cases m2 with
  | none =>
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rw [h2, h1]
  | some yg =>
    obtain ⟨y, g⟩ := yg
    simp only
    rw [h2, h2]
    cases (!(g != cR)) <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
      (try rw [h1])

end SIS.Tree
