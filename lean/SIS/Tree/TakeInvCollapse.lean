/-
Root collapse keeps the take-back's (B) (bergdb 024-12, TP4; TakeBackRun.lean)
in the form every rule keeps, `TtReachedN`: a node with a klong of the
transaction's time is reached. The root collapse's loop `writerWP_collapseRoot_inv`
with the take-back's facts in its invariant; the root that gives way is taken
back (`takeBackRoot`) or
keeps no klong of the transaction's time (`unlink`, `unlinked_no_time`).
-/
import SIS.Tree.TakeInvTree
import SIS.Tree.WriterKindsRules

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- `unlink` of a cached node: its klongs of the transaction dropped if its last
time is the transaction's, nothing else changed. -/
theorem writerWP_unlink_fate (x : NodeId) (n : KNode) (c : Ctx) (w : W)
    (hx : w.nodes.lookup x = some n) :
    WriterWP (unlink x) c w (fun _ v => v.taken = w.taken ∧ v.top = w.top ∧ v.vals = w.vals ∧
      v.nodes.lookup x = some (if n.lastTime == some c.i then n.toPrev (c.i - 1) else n) ∧
      (∀ y, y ≠ x → v.nodes.lookup y = w.nodes.lookup y)) := by
  unfold unlink
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known x n c w hx]
  split
  · rename_i h
    simp only [putNode, writerWP_modify]
    refine ⟨trivial, trivial, trivial, ?_, ?_⟩
    · simp only [lookup_upsert, ↓reduceIte]
    · intro y hy
      simp only [lookup_upsert, hy, ↓reduceIte]
  · rename_i h
    simp only [writerWP_pure]
    refine ⟨trivial, trivial, trivial, ?_, fun _ _ => trivial⟩
    exact hx

/-! ## Live klongs of a repointed or extended leaf -/

theorem KNode.repoint_liveAt_new (n : KNode) (x y : NodeId) (k j : Nat) (t : Time)
    (hj : n.linkIndex x k = some j) (ht : ∀ s, Klong.time s ∈ n.ks → s ≤ t) :
    (k, y) ∈ (n.repoint j y).liveAt t := by
  rw [KNode.liveAt_of_times _ t (KNode.repoint_times n j y t ht)]
  apply mem_of_lookup_nodup
  rw [KNode.repoint_live_lookup n x y k j hj k]
  simp

theorem KNode.repoint_liveAt_keep (n : KNode) (x y : NodeId) (k j : Nat) (t : Time)
    (hj : n.linkIndex x k = some j) (ht : ∀ s, Klong.time s ∈ n.ks → s ≤ t) (c : Nat) (z : NodeId)
    (hz : (c, z) ∈ n.liveAt t) (hck : c ≠ k) : (c, z) ∈ (n.repoint j y).liveAt t := by
  rw [KNode.liveAt_of_times _ t (KNode.repoint_times n j y t ht)]
  rw [KNode.liveAt_of_times n t ht] at hz
  apply mem_of_lookup_nodup
  rw [KNode.repoint_live_lookup n x y k j hj c]
  have hb : (k == c) = false := by simpa using Ne.symm hck
  rw [hb]
  simpa using lookup_of_mem_nodup _ (KNode.live_keys_nodup _) c z hz

theorem KNode.add_liveAt_new (n : KNode) (k : Nat) (y : NodeId) (t : Time)
    (hw : klongsWf n.ks = true) (ht : ∀ s, Klong.time s ∈ n.ks → s ≤ t) :
    (k, y) ∈ (n.add t (.key k y)).liveAt t := by
  rw [KNode.liveAt_of_times _ t (KNode.add_times n t (.key k y) (fun s h => by cases h) ht)]
  apply mem_of_lookup_nodup
  rw [KNode.add_key_live_lookup_of_wf n t k k y hw]
  simp

theorem KNode.add_liveAt_keep (n : KNode) (k : Nat) (y : NodeId) (t : Time)
    (hw : klongsWf n.ks = true) (ht : ∀ s, Klong.time s ∈ n.ks → s ≤ t) (c : Nat) (z : NodeId)
    (hz : (c, z) ∈ n.liveAt t) (hck : c ≠ k) : (c, z) ∈ (n.add t (.key k y)).liveAt t := by
  rw [KNode.liveAt_of_times _ t (KNode.add_times n t (.key k y) (fun s h => by cases h) ht)]
  rw [KNode.liveAt_of_times n t ht] at hz
  apply mem_of_lookup_nodup
  rw [KNode.add_key_live_lookup_of_wf n t k c y hw]
  have hb : (k == c) = false := by simpa using Ne.symm hck
  rw [hb]
  simpa using lookup_of_mem_nodup _ (KNode.live_keys_nodup _) c z hz

/-! ## The steps at a segment root -/

/-! ## The steps at the space root, and the loop -/

theorem writerWP_replaceRoot_spaceT (x : NodeId) (only : Nat) (n : KNode) (child : NodeId) (c : Ctx)
    (w : W) (hlk : w.nodes.lookup x = some n) (hptr : n.ptr? only = some child) :
    WriterWP (replaceRoot x 0 only) c w (fun _ w' => w'.top.rootKey = child ∧ w'.taken = w.taken ∧
      w'.vals = w.vals ∧
      w'.nodes.lookup x = some (if n.lastTime == some c.i then n.toPrev (c.i - 1) else n) ∧
      ∀ y, y ≠ x → w'.nodes.lookup y = w.nodes.lookup y) := by
  unfold replaceRoot
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known x n c w hlk]
  rw [hptr]
  simp only [note, writerWP_bind, writerWP_modify]
  refine writerWP_mono (writerWP_unlink_fate x n c _ (by simpa using hlk)) ?_
  intro _ w1 ⟨h1t, _, h1v, h1x, h1l⟩
  refine writerWP_mono (writerWP_newSuperRoot_frameV child c w1) ?_
  intro _ w2 ⟨h2r, h2t, h2n, h2v⟩
  exact ⟨h2r, by rw [h2t, h1t], by rw [h2v, h1v], by rw [h2n, h1x],
    fun y hy => by rw [h2n, h1l y hy]⟩

end SIS.Tree
