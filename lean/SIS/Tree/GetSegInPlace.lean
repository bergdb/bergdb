import SIS.Tree.GetNewSeg
import SIS.Tree.WriterTreeRepoint

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! A put into a segment's root L, a full leaf that the transaction made, below
the segment leaf q of the key's segment before (bergdb 024-12, TP10; `OpGetOK`'s
rules): the space split in place keeps the first half at L, makes the second
and a new segment root, and repoints q's klong to L in place
(`split.space2.inplace`). -/

theorem KNode.linkIndex_split (n : KNode) (x : NodeId) (c0 j : Nat)
    (hj : n.linkIndex x c0 = some j) :
    ∃ pre post, n.ks = pre ++ Klong.key c0 x :: post ∧ pre.length = j ∧
      (∀ k ∈ post, ∀ y, k ≠ Klong.key c0 y) ∧ n.lastBitmap.contains j = false := by
  unfold KNode.linkIndex at hj
  dsimp only at hj
  split at hj
  · rename_i c' y' i hf
    split at hj
    · rename_i hc
      have hij : i = j := Option.some.inj hj
      subst hij
      simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, beq_iff_eq] at hc
      obtain ⟨hdel, hy⟩ := hc
      subst hy
      obtain ⟨hp, as, bs, hrev, has⟩ := List.find?_eq_some_iff_append.mp hf
      simp only [beq_iff_eq] at hp
      subst hp
      have hz : n.ks.zipIdx = bs.reverse ++ (Klong.key c' y', i) :: as.reverse := by
        have := congrArg List.reverse hrev
        simpa using this
      obtain ⟨l1, l2, hks, h1, h2⟩ := List.zipIdx_eq_append_iff.mp hz
      obtain ⟨a, rest, hl2, ha, hrest⟩ := List.zipIdx_eq_cons_iff.mp h2.symm
      simp only [Prod.mk.injEq, Nat.zero_add] at ha
      obtain ⟨ha1, ha2⟩ := ha
      subst hl2
      refine ⟨l1, rest, by rw [hks, ha1], ha2.symm, ?_, hdel⟩
      intro k hk y hky
      subst hky
      obtain ⟨m, hm⟩ : ∃ m, (Klong.key c' y, m) ∈ rest.zipIdx (l1.length + 1) := by
        obtain ⟨m, hm⟩ := List.mem_iff_getElem.mp hk
        refine ⟨l1.length + 1 + m, ?_⟩
        apply List.mem_iff_getElem.mpr
        refine ⟨m, by simpa using hm.1, ?_⟩
        simp [hm.2]
      have hm' : (Klong.key c' y, m) ∈ as.reverse := by
        rw [hrest]; simpa using hm
      have := has (Klong.key c' y, m) (by simpa using hm')
      simp at this
    · cases hj
  · cases hj

theorem keyLookupFold_no_key (del : List Nat) (c0 : Nat) :
    ∀ (post : List Klong) (k : Nat) (v : Option NodeId), (∀ q ∈ post, ∀ y, q ≠ Klong.key c0 y) →
      (post.zipIdx k).foldl (keyLookupStep del c0) v = v := by
  intro post
  induction post with
  | nil => intro k v _; rfl
  | cons q rest ih =>
    intro k v h
    simp only [List.zipIdx_cons, List.foldl_cons]
    have hq : keyLookupStep del c0 v (q, k) = v := by
      unfold keyLookupStep
      cases q with
      | key a z =>
        simp only
        have : (a == c0) = false := by
          cases hb : (a == c0) with
          | false => rfl
          | true => exact absurd (by rw [beq_iff_eq.mp hb]) (h (Klong.key a z) List.mem_cons_self z)
        simp [this]
      | time t => rfl
      | del b => rfl
    rw [hq]
    exact ih (k + 1) v (fun q' hq' => h q' (List.mem_cons_of_mem _ hq'))

/-- A klong repointed in place at the index that `linkIndex` gives for c0: the
live klong of c0 names the new node, every other is the node's. -/
theorem KNode.repoint_live_lookup (n : KNode) (x y : NodeId) (c0 j : Nat)
    (hj : n.linkIndex x c0 = some j) (c : Nat) :
    (n.repoint j y).live.lookup c = if c0 == c then some y else n.live.lookup c := by
  obtain ⟨pre, post, hks, hlen, hpost, hdel⟩ := KNode.linkIndex_split n x c0 j hj
  have hget : n.ks[j]? = some (Klong.key c0 x) := by
    rw [hks, ← hlen]; simp
  have hrep : n.repoint j y = { n with ks := pre ++ Klong.key c0 y :: post } := by
    unfold KNode.repoint
    rw [hget]
    simp only [KNode.setAt, hks, ← hlen]
    congr 1
    simp
  have hbm : (n.repoint j y).lastBitmap = n.lastBitmap := by
    unfold KNode.lastBitmap
    rw [hrep]
    simp only
    have := lastBitmapOf_set_key n.ks j c0 y ⟨x, hget⟩
    rw [← this, hks, ← hlen]
    simp
  rw [KNode.live_lookup, KNode.live_lookup, hbm]
  unfold keyLookup
  rw [hrep]
  simp only
  rw [hks]
  simp only [List.zipIdx_append, List.zipIdx_cons, List.foldl_append, List.foldl_cons,
    Nat.zero_add, hlen]
  by_cases hc : c0 = c
  · subst hc
    simp only [beq_self_eq_true, ↓reduceIte]
    have hs : keyLookupStep n.lastBitmap c0 ((pre.zipIdx).foldl (keyLookupStep n.lastBitmap c0) none)
        (Klong.key c0 y, j) = some y := by
      have hdel' : j ∉ n.lastBitmap := by simpa using hdel
      unfold keyLookupStep
      simp [hdel']
    rw [hs]
    exact keyLookupFold_no_key _ _ post (j + 1) (some y) hpost
  · have hb : (c0 == c) = false := by simpa using hc
    simp only [hb, Bool.false_eq_true, ↓reduceIte]
    congr 1
    unfold keyLookupStep
    simp [hb]

end SIS.Tree
