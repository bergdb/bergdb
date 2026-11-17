/-
The parent's own split with the hole below it, at the writer (bergdb 030-01, R4's open
part), for the group of l4f's 69 thin-copy cascades whose segment leaf q the transaction
made (7 on the runs): p's copy y put by `appendKlongs` into q, without room (or
compacting) and within a split's bound, makes q split in time in place (`split.time.inplace`):
q holds its last version with p's klong naming y, nothing else changes. What
`descendToHeight_redirectSeg` (02:22) takes: q's node is a leaf whose search of p's klong
names y, the other nodes kept.
-/
import SIS.Tree.LiveTimeRoomHole

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- The post of an in-place time split with p's copy put: q's new node is a leaf (as q)
whose search of k1 names y; the other nodes, the top and the taken set kept. -/
theorem inPlaceHole_post (c : Ctx) (w w' : W) (q : NodeId) (n : KNode) (k1 : Nat) (y : NodeId)
    (l : KNode) (hl1 : l.leaf = n.leaf) (hl2 : klongsWf l.ks = true)
    (hl3 : ∀ s, Klong.time s ∈ l.ks → s ≤ c.i)
    (hl4 : ∀ q', l.live.lookup q' = [(k1, y)].foldl (pairLookupStep q') (n.live.lookup q'))
    (hnodes : w'.nodes = upsert w.nodes q ⟨n.leaf, l.ks⟩) :
    (∀ z, z ≠ q → w'.nodes.lookup z = w.nodes.lookup z) ∧
    ∃ qn', rdN c w' q = some qn' ∧ qn'.leaf = n.leaf ∧
      ∃ fd', qn'.searchEq c.i k1 = some fd' ∧ fd'.y = y := by
  have hq : (⟨n.leaf, l.ks⟩ : KNode) = l := by rw [← hl1]
  refine ⟨fun z hz => by rw [hnodes, lookup_upsert]; simp [hz], l, ?_, hl1, ?_⟩
  · apply rdN_of_lookup
    rw [hnodes, lookup_upsert]
    simp [hq]
  · have hs := KNode.searchEq_live l c.i hl2 hl3 k1
    rw [hl4 k1] at hs
    simp only [List.foldl_cons, List.foldl_nil, pairLookupStep, beq_self_eq_true, ↓reduceIte] at hs
    obtain ⟨fd', hfd', hfy⟩ := Option.map_eq_some_iff.mp hs
    exact ⟨fd', hfd', hfy⟩

/-- p's copy y put by k1 into q (at depth d'' + 1), made by the transaction, without room
(or compacting), its last version within a split's bound when it has no room: q splits
in time in place; q's node is a leaf whose search of k1 names y; the rest kept. -/
theorem writerWP_appendKlongs_timeInPlaceHole (d'' : Nat) (q q0 : NodeId) (n q0n : KNode)
    (k1 : Nat) (y : NodeId) (c : Ctx) (w : W)
    (hlk : w.nodes.lookup q = some n) (hlq0 : w.nodes.lookup q0 = some q0n)
    (hpq : (w.path[d'']?).map (·.2) = some q0) (hfirst : n.firstTime = some c.i)
    (hfull : n.size + 2 ≤ c.p.M → deadOver c.p (n.add c.i (.key k1 y)) = true)
    (htime : c.p.M < n.size + 2 → (n.lastVersion c.i).size ≤ c.p.splitAbove) :
    WriterWP (appendKlongs (d'' + 1) q [(k1, y)]) c w (fun _ w' =>
      w'.taken = w.taken ∧ w'.top = w.top ∧ w'.path = w.path ∧
      (∀ z, z ≠ q → w'.nodes.lookup z = w.nodes.lookup z) ∧
      ∃ qn', rdN c w' q = some qn' ∧ qn'.leaf = n.leaf ∧
        ∃ fd', qn'.searchEq c.i k1 = some fd' ∧ fd'.y = y) := by
  have hsplit : ∀ compact : Bool,
      (!compact && decide ((n.lastVersion c.i).size > c.p.splitAbove)) = false →
      WriterWP (handleFullWith (fun q more => appendKlongs d'' q more) (d'' + 1) q [(k1, y)]
        (n.lastVersion c.i) compact) c w (fun _ w' =>
      w'.taken = w.taken ∧ w'.top = w.top ∧ w'.path = w.path ∧
      (∀ z, z ≠ q → w'.nodes.lookup z = w.nodes.lookup z) ∧
      ∃ qn', rdN c w' q = some qn' ∧ qn'.leaf = n.leaf ∧
        ∃ fd', qn'.searchEq c.i k1 = some fd' ∧ fd'.y = y) := by
    intro compact hcs
    refine writerWP_mono (writerWP_handleFullWith_timeInPlace_termN _ d'' q q0 n q0n [(k1, y)]
      compact c w hlk hlq0 hpq hfirst hcs) ?_
    rintro _ w' ⟨l, hl1, hl2, hl3, hl4, -, ht, htop, -, -, hp, hn⟩
    exact ⟨ht, htop, hp, inPlaceHole_post c w w' q n k1 y l hl1 hl2 hl3 hl4 hn⟩
  rw [appendKlongs_step_dead]
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known _ _ c w hlk]
  by_cases hsz : n.size + [(k1, y)].length + 1 > c.p.M
  · simp only [hsz, ↓reduceIte]
    have h2 := htime (by simpa using hsz)
    exact hsplit false
      (by simp only [Bool.not_false, Bool.true_and, decide_eq_false_iff_not, gt_iff_lt]; omega)
  · have hd := hfull (by simp at hsz; omega)
    simp only [List.foldl_cons, List.foldl_nil] at hsz ⊢
    simp only [hsz, hd, ↓reduceIte]
    exact hsplit true (by simp)

/-- The same at the space root q (depth 0), made by the transaction. -/
theorem writerWP_appendKlongs_rootInPlaceHole (q : NodeId) (n : KNode)
    (k1 : Nat) (y : NodeId) (c : Ctx) (w : W)
    (hlk : w.nodes.lookup q = some n) (hfirst : n.firstTime = some c.i)
    (hfull : n.size + 2 ≤ c.p.M → deadOver c.p (n.add c.i (.key k1 y)) = true)
    (htime : c.p.M < n.size + 2 → (n.lastVersion c.i).size ≤ c.p.splitAbove) :
    WriterWP (appendKlongs 0 q [(k1, y)]) c w (fun _ w' =>
      w'.taken = w.taken ∧ w'.top = w.top ∧ w'.path = w.path ∧
      (∀ z, z ≠ q → w'.nodes.lookup z = w.nodes.lookup z) ∧
      ∃ qn', rdN c w' q = some qn' ∧ qn'.leaf = n.leaf ∧
        ∃ fd', qn'.searchEq c.i k1 = some fd' ∧ fd'.y = y) := by
  have hsplit : ∀ compact : Bool,
      (!compact && decide ((n.lastVersion c.i).size > c.p.splitAbove)) = false →
      WriterWP (handleFullWith (fun _ _ => throw "corrupt: a split's parent above depth 0") 0 q
        [(k1, y)] (n.lastVersion c.i) compact) c w (fun _ w' =>
      w'.taken = w.taken ∧ w'.top = w.top ∧ w'.path = w.path ∧
      (∀ z, z ≠ q → w'.nodes.lookup z = w.nodes.lookup z) ∧
      ∃ qn', rdN c w' q = some qn' ∧ qn'.leaf = n.leaf ∧
        ∃ fd', qn'.searchEq c.i k1 = some fd' ∧ fd'.y = y) := by
    intro compact hcs
    refine writerWP_mono (writerWP_handleFullWith_timeInPlace_term0N _ q n [(k1, y)]
      compact c w hlk hfirst hcs) ?_
    rintro _ w' ⟨l, hl1, hl2, hl3, hl4, -, ht, htop, -, -, hp, hn⟩
    exact ⟨ht, htop, hp, inPlaceHole_post c w w' q n k1 y l hl1 hl2 hl3 hl4 hn⟩
  rw [appendKlongs_step_dead]
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known _ _ c w hlk]
  by_cases hsz : n.size + [(k1, y)].length + 1 > c.p.M
  · simp only [hsz, ↓reduceIte]
    have h2 := htime (by simpa using hsz)
    exact hsplit false
      (by simp only [Bool.not_false, Bool.true_and, decide_eq_false_iff_not, gt_iff_lt]; omega)
  · have hd := hfull (by simp at hsz; omega)
    simp only [List.foldl_cons, List.foldl_nil] at hsz ⊢
    simp only [hsz, hd, ↓reduceIte]
    exact hsplit true (by simp)

end SIS.Tree
