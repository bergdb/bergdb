/-
The writer's merge keeps the writer's tree (bergdb 024-22, `OpTreeOK`;
024-11, M1 to M5): `merge x d` with a parent that has room and no compaction,
of two nodes that the transaction did not make.
-/
import SIS.Tree.WriterTreeMergeW

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- The merge after its two nodes are chosen: the code of `merge` from its note
of the side on. -/
def mergeTail (c : Ctx) (x : NodeId) (d : Nat) (p : NodeId) (pn xn : KNode) (leftSome : Bool)
    (l : NodeId) (ln : KNode) (il : Nat) (r : NodeId) (rn : KNode) (ir : Nat) : M Nat := do
  let tt := c.i
  let inner := !xn.leaf
  note (if leftSome then "merge.left" else "merge.right")
  let cL ← match pn.cv? il with
    | some v => pure v
    | none => throw s!"Bug: merge at {tt}: no klong {il} in {p}"
  let cR ← match pn.cv? ir with
    | some v => pure v
    | none => throw s!"Bug: merge at {tt}: no klong {ir} in {p}"
  let lvL := ln.live
  let lvR := rn.live
  if lvL.isEmpty || lvR.isEmpty then
    throw s!"Bug: merge at {tt}: key node {l} or {r} has no live klong"
  if inner && ((lvL.head?.map (·.1)) != some 0 || (lvR.head?.map (·.1)) != some 0) then
    throw s!"Bug: merge at {tt}: inner node {l} or {r} has no live klong of the empty key first"
  let (first, second) := mergeKlongs inner c.p.mergeMax cR lvL lvR
  modify (fun w => { w with merges := w.merges + 1 })
  note (if second.isSome then "merge.two" else "merge.one")
  note (if inner then "merge.inner" else "merge.leaf")
  let (g, h) ← ghOf x
  let lMade := ln.firstTime == some tt
  let rMade := rn.firstTime == some tt
  if lMade then note "merge.made.left"
  if rMade then note "merge.made.right"
  let m1 ← newKey g h (!inner) (newKlongs tt first)
  setMadeFor m1 (← if lMade then replacedBy l else pure (some l))
  let m2 ← match second with
    | some (ks2, g2) => do
      let y ← newKey g h (!inner) (newKlongs tt ks2)
      setMadeFor y (← if rMade then replacedBy r else pure (some r))
      pure (some (y, g2))
    | none => pure none
  mergeParent p (d - 1) il cL m1 ir cR m2
  for (o, made) in [(l, lMade), (r, rMade)] do
    if made then
      retarget p o m1
      takenBack o
      note "merge.takeback"
    else unlink o
  pure (if second.isSome then 2 else 1)

theorem writerWP_ghOf_frame (x : NodeId) (c : Ctx) (w : W) :
    WriterWP (ghOf x) c w (fun _ w' => w'.taken = w.taken ∧ w'.top = w.top ∧
      w'.next = w.next ∧ w'.vals = w.vals ∧ w'.path = w.path ∧ w'.madeFor = w.madeFor ∧
      ∀ y, y ≠ x → w'.nodes.lookup y = w.nodes.lookup y) := by
  unfold ghOf
  simp only [writerWP_bind]
  refine writerWP_mono (writerWP_getNode_frame x c w) ?_
  intro _ w1 h1
  simp only [writerWP_get]
  split
  · simp only [writerWP_pure]; exact h1
  · exact writerWP_throw _ _ _ _

theorem KNode.repoint_times (n : KNode) (i : Nat) (y : NodeId) (t : Time)
    (h : ∀ s, Klong.time s ∈ n.ks → s ≤ t) : ∀ s, Klong.time s ∈ (n.repoint i y).ks → s ≤ t := by
  intro s hs
  unfold KNode.repoint at hs
  split at hs
  · simp only [KNode.setAt] at hs
    rcases List.mem_or_eq_of_mem_set hs with h1 | h1
    · exact h s h1
    · cases h1
  · exact h s hs

theorem mpNode_times (pn : KNode) (tt : Time) (il cL : Nat) (m1 : NodeId) (ir cR : Nat)
    (m2 : Option (NodeId × Nat)) (htd lip rip : Bool)
    (htdh : htd = true → ∃ old, pn.ks.getLast? = some (.del old))
    (h : ∀ s, Klong.time s ∈ pn.ks → s ≤ tt) :
    ∀ s, Klong.time s ∈ (mpNode pn tt il cL m1 ir cR m2 htd lip rip).ks → s ≤ tt := by
  have hn1 : ∀ (b : Bool) (U : List Nat), ∀ s, Klong.time s ∈ (if !b then pn else if htd then
      pn.setAt (pn.size - 1) (.del U) else pn.add tt (.del U)).ks → s ≤ tt := by
    intro b U
    have hA : ∀ s, Klong.time s ∈ (if htd then pn.setAt (pn.size - 1) (.del U)
        else pn.add tt (.del U)).ks → s ≤ tt := by
      cases htd with
      | true => obtain ⟨old, hl⟩ := htdh rfl; exact KNode.setAt_last_del_times pn tt old U hl h
      | false => exact KNode.add_times pn tt _ (fun s h => by cases h) h
    cases b with
    | false => exact h
    | true => exact hA
  have hn2 : ∀ n1 : KNode, (∀ s, Klong.time s ∈ n1.ks → s ≤ tt) →
      ∀ s, Klong.time s ∈ (if lip then n1.repoint il m1 else n1.add tt (.key cL m1)).ks → s ≤ tt := by
    intro n1 h1
    cases lip with
    | true => simp only [↓reduceIte]; exact KNode.repoint_times n1 il m1 tt h1
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact KNode.add_times n1 tt _ (fun s h => by cases h) h1
  unfold mpNode
  cases m2 with
  | none => exact hn2 _ (hn1 _ _)
  | some yg =>
    obtain ⟨y, g⟩ := yg
    simp only
    cases rip with
    | true => simp only [↓reduceIte]; exact KNode.repoint_times _ ir y tt (hn2 _ (hn1 _ _))
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact KNode.add_times _ tt _ (fun s h => by cases h) (hn2 _ (hn1 _ _))

theorem htd_last (pn : KNode) (b : Bool)
    (h : ((match pn.ks.getLast? with
      | some (.del _) => true
      | _ => false) && b) = true) : ∃ old, pn.ks.getLast? = some (.del old) := by
  cases hg : pn.ks.getLast? with
  | none => rw [hg] at h; simp at h
  | some k =>
    cases k with
    | del old => exact ⟨old, rfl⟩
    | time t => rw [hg] at h; simp at h
    | key a y => rw [hg] at h; simp at h

theorem lookup_of_prefix (l1 l2 : List (NodeId × KNode)) (h : l1 <+: l2) (y : NodeId) (v : KNode)
    (hv : l1.lookup y = some v) : l2.lookup y = some v := by
  obtain ⟨t, rfl⟩ := h
  rw [List.lookup_append, hv]; rfl

/-- `getNode` reads: the node's lookup after, the reading unchanged, the
writer's nodes extended by nodes of P@(i - 1) at most. -/
theorem writerWP_getNode_all (x : NodeId) (c : Ctx) (w : W) (base : View BVal)
    (hvc : ViewCoherent c base) :
    WriterWP (getNode x) c w (fun n v => ReadsAs c.p base w v ∧ v.nodes.lookup x = some n ∧
      (w.taken.contains x = false → wNode c.p base w x = some n) ∧ w.nodes <+: v.nodes ∧
      (∀ z, (v.nodes.lookup z).isSome = true → (w.nodes.lookup z).isSome = true ∨
        (c.view z).isSome = true)) := by
  refine writerWP_mono (writerWP_and (writerWP_getNode_reads x c w base hvc)
    (writerWP_getNode_cache2 x c w)) ?_
  intro n v ⟨⟨h1, h2, h3⟩, h4, h5⟩
  exact ⟨h1, h2, h3, h4, h5⟩

end SIS.Tree
