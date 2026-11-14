/-
The writer's tree kept by its rules (bergdb 024-22, `OpTreeOK`). Here the first
rule: a put of a key of one segment into a segment leaf with room
(`writerWP_put_room_tree`), the case of `GetFrame.lean`'s `writerWP_put_room`:
the leaf's klong of the key names the new value, which nothing named before.
-/
import SIS.Tree.WriterTreeVisits

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! ## Lists and nodes -/

/-- A key klong added at time t keeps every other live klong at t. -/
theorem KNode.add_key_liveAt_other (n : KNode) (t : Time) (cv : Nat) (v : NodeId)
    (hw : klongsWf n.ks = true) (ht : ∀ s, Klong.time s ∈ n.ks → s ≤ t) (c : Nat) (y : NodeId)
    (hc : c ≠ cv) (h : (c, y) ∈ (n.add t (.key cv v)).liveAt t) : (c, y) ∈ n.liveAt t := by
  have ht' := KNode.add_times n t (.key cv v) (fun s h => by cases h) ht
  rw [KNode.liveAt_eq_live_prefix,
    prefixAt_of_times _ t (fun k hk s hs => by subst hs; exact ht' s hk)] at h
  rw [KNode.liveAt_eq_live_prefix, prefixAt_of_times n.ks t (fun k hk s hs => by subst hs; exact ht s hk)]
  have hl := lookup_of_mem_nodup _ (KNode.live_keys_nodup _) c y h
  have hlk := KNode.add_key_live_lookup_of_wf n t cv c v hw
  have hb : (cv == c) = false := by simpa using (Ne.symm hc)
  simp only [hb, Bool.false_eq_true, ↓reduceIte] at hlk
  have hl' : (({ leaf := n.leaf, ks := n.ks } : KNode).live).lookup c = some y := by
    rw [← hlk]; exact hl
  exact mem_of_lookup_nodup _ c y hl'

/-- A key klong added at time t: the live klongs at t are the new one and the
others of the node. -/
theorem KNode.add_key_liveAt_mem (n : KNode) (t : Time) (cv : Nat) (v : NodeId)
    (hw : klongsWf n.ks = true) (ht : ∀ s, Klong.time s ∈ n.ks → s ≤ t) (c : Nat) (y : NodeId)
    (h : (c, y) ∈ (n.add t (.key cv v)).liveAt t) :
    (c = cv ∧ y = v) ∨ (c ≠ cv ∧ (c, y) ∈ n.liveAt t) := by
  by_cases hc : c = cv
  · subst hc
    left
    refine ⟨rfl, ?_⟩
    have ht' := KNode.add_times n t (.key c v) (fun s h => by cases h) ht
    rw [KNode.liveAt_eq_live_prefix,
      prefixAt_of_times _ t (fun k hk s hs => by subst hs; exact ht' s hk)] at h
    have hl := lookup_of_mem_nodup _ (KNode.live_keys_nodup _) c y h
    have hl2 : ({ leaf := (n.add t (.key c v)).leaf, ks := (n.add t (.key c v)).ks } : KNode).live.lookup c =
        (n.add t (.key c v)).live.lookup c := rfl
    rw [hl2, KNode.add_key_live_lookup_of_wf n t c c v hw] at hl
    simp at hl
    exact hl.symm
  · exact Or.inr ⟨hc, KNode.add_key_liveAt_other n t cv v hw ht c y hc h⟩

/-! ## A change whose links are links of the tree -/

/-- A change whose links, from the nodes it reaches, are links of the tree
keeps the tree. -/
theorem treeOK_of_sublinks (L L' : NodeId → Option KNode) (t : Time) (r : NodeId)
    (ht : TreeOK L t r) (hroot : ∃ n, L' r = some n)
    (hsub : ∀ x c y, TLink L' t x c y → TLink L t x c y) : TreeOK L' t r := by
  have hb : ∀ y, TReach L' t r y → TReach L t r y := by
    intro y hy
    induction hy with
    | root => exact TReach.root
    | link _ hl ih => exact TReach.link ih (hsub _ _ _ hl)
  refine ⟨hroot, ?_, ?_⟩
  · intro x c hx hl
    exact ht.rootFree x c (hb x hx) (hsub x c r hl)
  · intro x c x' c' y hx hx' hl hl'
    exact ht.oneLink x c x' c' y (hb x hx) (hb x' hx') (hsub x c y hl) (hsub x' c' y hl')

/-- A node that is no node of the lookup and that no link of the tree names is
not reached (a fresh id). -/
theorem not_reach_fresh (L : NodeId → Option KNode) (t : Time) (r y : NodeId)
    (ht : TreeOK L t r) (hy : L y = none) (hf : ∀ u c, TReach L t r u → ¬ TLink L t u c y) :
    ¬ TReach L t r y := by
  intro h
  cases h with
  | root => obtain ⟨m, hm⟩ := ht.rootKey; rw [hm] at hy; cases hy
  | link hu hl => exact hf _ _ hu hl

/-! ## A put into a segment leaf with room -/

end SIS.Tree
