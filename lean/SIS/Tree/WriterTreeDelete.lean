/-
The writer's tree kept by a delete's bitmap (bergdb 024-22, `OpTreeOK`): the
bitmap that deletes a compare value in a node with room, new or the
transaction's own in place, drops that compare value's klong and keeps every
other; a node whose live klongs only
shrink keeps the tree (`treeOK_of_node_shrink`).
-/
import SIS.Tree.WriterTreeSpace

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- A node whose live klongs at the latest time are a node's without one
compare value: at a time after both their klongs, the live klongs are among the
node's. -/
theorem liveAt_sub_of_lookup (n n' : KNode) (t : Time) (cv : Nat)
    (hn : ∀ s, Klong.time s ∈ n.ks → s ≤ t) (hn' : ∀ s, Klong.time s ∈ n'.ks → s ≤ t)
    (hl : ∀ c, n'.live.lookup c = if c == cv then none else n.live.lookup c)
    (c : Nat) (z : NodeId) (h : (c, z) ∈ n'.liveAt t) : c ≠ cv ∧ (c, z) ∈ n.liveAt t := by
  rw [KNode.liveAt_of_times n' t hn'] at h
  rw [KNode.liveAt_of_times n t hn]
  have h1 := lookup_of_mem_nodup _ (KNode.live_keys_nodup _) c z h
  rw [hl c] at h1
  by_cases hc : c = cv
  · subst hc; simp at h1
  · have hb : (c == cv) = false := by simpa using hc
    rw [hb] at h1
    simp only [Bool.false_eq_true, ↓reduceIte] at h1
    exact ⟨hc, mem_of_lookup_nodup _ c z h1⟩

/-- One node changed, its links only fewer: the tree is kept. -/
theorem treeOK_of_node_shrink (L L' : NodeId → Option KNode) (t : Time) (r x : NodeId)
    (n n' : KNode) (ht : TreeOK L t r) (hx : L x = some n) (hx' : L' x = some n')
    (hother : ∀ y, y ≠ x → L' y = L y)
    (hsub : ∀ c z, (c, z) ∈ n'.liveAt t → (c, z) ∈ n.liveAt t) : TreeOK L' t r := by
  apply treeOK_of_sublinks L L' t r ht
  · by_cases hr : r = x
    · rw [hr, hx']; exact ⟨_, rfl⟩
    · rw [hother r hr]; exact ht.rootKey
  · intro y c z hl
    obtain ⟨m, hm, hc⟩ := hl
    by_cases hy : y = x
    · subst hy
      rw [hx'] at hm
      simp only [Option.some.injEq] at hm
      subst hm
      exact ⟨n, hx, hsub c z hc⟩
    · rw [hother y hy] at hm
      exact ⟨m, hm, hc⟩

/-- The time klongs of a node's last klong replaced by a bitmap are the node's. -/
theorem KNode.setAt_last_del_times (n : KNode) (t : Time) (old bits : List Nat)
    (hlast : n.ks.getLast? = some (.del old)) (h : ∀ s, Klong.time s ∈ n.ks → s ≤ t) :
    ∀ s, Klong.time s ∈ (n.setAt (n.size - 1) (.del bits)).ks → s ≤ t := by
  obtain ⟨pre, hpre⟩ := List.getLast?_eq_some_iff.mp hlast
  rw [n.setAt_last_delete_ks pre old bits hpre]
  intro s hs
  rcases List.mem_append.mp hs with hs | hs
  · exact h s (by rw [hpre]; exact List.mem_append_left _ hs)
  · simp at hs

end SIS.Tree
