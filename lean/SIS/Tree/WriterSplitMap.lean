import SIS.Tree.SpaceSplitMap
import SIS.Tree.MergeProtectedMerge

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

theorem freshCache_lookup_none_ge (base : NodeId) (w : W) (hw : FreshCache base w)
    (x : NodeId) (hx : w.next ≤ x) : w.nodes.lookup x = none := by
  apply List.lookup_eq_none_iff.mpr
  intro q hq
  have hh := hw.2.1 q hq
  apply bne_iff_ne.mpr
  omega

set_option maxHeartbeats 1200000 in
/-- An in-place space split of the space root installs exactly the two
halves and the new parent, with no upward callback or merge. -/
theorem writerWP_handleFullWith_space_new_root_layout (base : NodeId) (b : NodeGuard)
    (up : NodeId → List (Nat × NodeId) → M Unit) (ins : List (Nat × NodeId))
    (last : KNode) (c : Ctx) (w : W) (hf : FreshCache base w) (hb : GuardHeld b w)
    (ht : b.node.firstTime = some c.i) (hfull : c.p.splitAbove < last.size) :
    let halvesOut := halves b.node.leaf c.i last ins
    let root : KNode := ⟨false, [.time c.i, .key 0 b.id, .key halvesOut.2.2 w.next]⟩
    WriterWP (handleFullWith up 0 b.id ins last false) c w (fun _ v =>
      v.nodes.lookup b.id = some halvesOut.1 ∧
      v.nodes.lookup w.next = some halvesOut.2.1 ∧
      v.nodes.lookup (w.next + 2) = some root ∧
      v.top.rootKey = w.next + 2 ∧
      v.spaceSplits = w.spaceSplits + 1 ∧ v.merges = w.merges ∧ v.taken = w.taken) := by
  dsimp only
  generalize hout : halves b.node.leaf c.i last ins = out
  have hn := hb.1
  have hg := hb.2.1
  have hx := hb.2.2.2
  have hbx : b.id ≠ w.next := by omega
  have hbx₂ : b.id ≠ w.next + 2 := by omega
  have hxb : w.next ≠ b.id := by omega
  have hx₂b : w.next + 2 ≠ b.id := by omega
  have hxx₂ : w.next ≠ w.next + 2 := by omega
  have hx₂x : w.next + 2 ≠ w.next := by omega
  have hnone := freshCache_lookup_none_ge base w hf w.next (by omega)
  have hnone₂ := freshCache_lookup_none_ge base w hf (w.next + 2) (by omega)
  have hnodes :
      let ns := upsert (upsert (w.nodes ++ [(w.next, ⟨b.node.leaf, []⟩)]) b.id out.1)
          w.next out.2.1 ++
        [(w.next + 2, ⟨false, [.time c.i, .key 0 b.id, .key out.2.2 w.next]⟩)]
      ns.lookup b.id = some out.1 ∧ ns.lookup w.next = some out.2.1 ∧
        ns.lookup (w.next + 2) =
          some ⟨false, [.time c.i, .key 0 b.id, .key out.2.2 w.next]⟩ := by
    dsimp only
    refine ⟨?_, ?_, ?_⟩
    · rw [List.lookup_append, upsert_lookup_other _ b.id w.next _ hbx,
        upsert_lookup_same]
      rfl
    · rw [List.lookup_append, upsert_lookup_same]
      rfl
    · rw [List.lookup_append,
        upsert_lookup_other _ (w.next + 2) w.next _ hx₂x,
        upsert_lookup_other _ (w.next + 2) b.id _ hx₂b]
      simp [List.lookup_append, hnone₂, List.lookup_cons, beq_eq_false_iff_ne.mpr hx₂x]
  unfold handleFullWith
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known b.id b.node c w hn,
    writerWP_ghOf_known b.id b.node b.g b.h c w hn hg]
  simp only [ht, BEq.rfl, parentAt, writerWP_pure, hfull, decide_true,
    Bool.not_false, Bool.true_and, Bool.false_eq_true, ↓reduceIte]
  unfold newKey fresh putNode replacedBy setMadeFor newSuperRoot note
  repeat' first
    | wpSimplify
    | simp only [hout]
    | simp only [note, fresh]
    | split
    | exact ⟨hnodes.1, hnodes.2.1, hnodes.2.2, trivial, trivial, trivial, trivial⟩
    | contradiction

/-- The actual split's cached children together implement the normalized
input map and all inserts, using the right child's local empty-key name. -/
theorem writerWP_handleFullWith_space_new_root_map (base : NodeId) (b : NodeGuard)
    (up : NodeId → List (Nat × NodeId) → M Unit) (pairs ins : List (Nat × NodeId))
    (c : Ctx) (w : W) (hf : FreshCache base w) (hb : GuardHeld b w)
    (ht : b.node.firstTime = some c.i) (hs : CvSorted pairs)
    (hfull : c.p.splitAbove < (⟨b.node.leaf, newKlongs c.i pairs⟩ : KNode).size)
    (r : Nat × NodeId) (hr : (pairs.drop (pairs.length / 2)).head? = some r)
    (hsc : 0 < r.1) (hside : ∀ q ∈ ins, decide (r.1 ≤ q.1) =
      (match ins.head? with | some a => decide (r.1 ≤ a.1) | none => false)) :
    WriterWP (handleFullWith up 0 b.id ins ⟨b.node.leaf, newKlongs c.i pairs⟩ false) c w
      (fun _ v => ∀ cv,
        ((v.nodes.lookup (if cv < r.1 then b.id else w.next)).bind
          (fun n => n.live.lookup (if cv < r.1 then cv else splitLocalCv b.node.leaf r.1 cv))) =
          ins.foldl (pairLookupStep cv) (pairs.lookup cv)) := by
  refine writerWP_mono
    (writerWP_handleFullWith_space_new_root_layout base b up ins
      ⟨b.node.leaf, newKlongs c.i pairs⟩ c w hf hb ht hfull) ?_
  rintro _ v ⟨hfirst, hsecond, hroot, htop, hsplits, hmerges, htaken⟩ cv
  have hmap := halves_lookup b.node.leaf c.i pairs ins hs r hr hsc hside cv
  have hdivider : (halves b.node.leaf c.i ⟨b.node.leaf, newKlongs c.i pairs⟩ ins).2.2 = r.1 := by
    rw [halves_shape b.node.leaf c.i pairs ins r hr]
    repeat' first | rfl | split
  dsimp only at hmap
  rw [hdivider] at hmap
  by_cases hc : cv < r.1
  · simp only [hc, ↓reduceIte, hfirst, Option.bind_some]
    simpa only [hc, ↓reduceIte] using hmap
  · simp only [hc, ↓reduceIte, hsecond, Option.bind_some]
    simpa only [hc, ↓reduceIte] using hmap

end SIS.Tree
