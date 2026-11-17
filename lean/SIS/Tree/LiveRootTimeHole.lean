/-
The parent's own split with the hole below it, at the writer (bergdb 030-01, R4's open
part), for the largest group of l4f's 69 thin-copy cascades (25 on the runs): the merge's
parent p, a segment root, split in time, its copy y the hole, put by `appendKlongs` into
its segment leaf q, the space root, not made by the transaction, without room (or
compacting) and split in time (`split.time2`): q's copy, its last version with p's klong
naming y, becomes the space root. Its shape (`writerWP_handleFullWith_rootTimeSplit_ins`,
`writerWP_appendKlongs_rootTime`) gives what `descendToHeight_topSeg_leafRoot` takes: the new
space root is a leaf whose search of p's klong names y. The live counts after the split,
the copy the hole, are `writerWP_appendKlongs_chainGLX`'s with E the copy.
-/
import SIS.Tree.LiveRedirectTopSeg
import SIS.Tree.ChainShape
import SIS.Tree.PutInvDelRoot

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

set_option maxHeartbeats 4000000 in
/-- The time split of the space root L, not made by the transaction, with klongs ins to
put and its last version: the next id holds the last version with ins (`out`), the new
space root; L its klongs before the transaction; the rest kept. -/
theorem writerWP_handleFullWith_rootTimeSplit_ins (up : NodeId → List (Nat × NodeId) → M Unit)
    (L : NodeId) (n : KNode) (ins : List (Nat × NodeId)) (compact : Bool) (c : Ctx) (w : W)
    (hlk : w.nodes.lookup L = some n) (hfirst : n.firstTime ≠ some c.i)
    (hcs : (!compact && decide ((n.lastVersion c.i).size > c.p.splitAbove)) = false)
    (hLn : L < w.next) (hny : w.nodes.lookup w.next = none) :
    WriterWP (handleFullWith up 0 L ins (n.lastVersion c.i) compact) c w (fun _ w' =>
      w'.taken = w.taken ∧ w'.top.rootKey = w.next ∧ ∃ out : KNode,
        out.leaf = n.leaf ∧ klongsWf out.ks = true ∧ (∀ s, Klong.time s ∈ out.ks → s ≤ c.i) ∧
        (∀ q, out.live.lookup q = ins.foldl (pairLookupStep q) (n.live.lookup q)) ∧
        ∀ x, w'.nodes.lookup x =
          if x = L then some (n.toPrev (c.i - 1))
          else if x = w.next then some ⟨n.leaf, out.ks⟩ else w.nodes.lookup x) := by
  unfold handleFullWith
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known L n c w hlk]
  refine writerWP_ghOf_cached L n c w hlk _ (fun gh => ?_)
  have hnew : (n.firstTime == some c.i) = false := by simpa using hfirst
  simp only [hnew, parentAt, writerWP_pure, hcs, Bool.false_eq_true, ↓reduceIte, Bool.not_false]
  have hL1 : L ≠ w.next := by omega
  split <;>
  · simp only [note, writerWP_bind, writerWP_modify, writerWP_pure]
    refine writerWP_mono (writerWP_replaceOrAdd_lastN n ins c _) ?_
    rintro l w1 ⟨hw1, hl1, hl2, hl3, hl4, -⟩
    subst w1
    split <;>
    · simp only [newKey, fresh, setMadeFor, note, newSuperRoot, writerWP_bind, writerWP_modify,
        writerWP_get, writerWP_set, writerWP_read, writerWP_pure]
      split <;>
      · simp only [writerWP_bind, writerWP_modify, writerWP_pure]
        split <;>
        · simp only [writerWP_bind, writerWP_modify, writerWP_pure, writerWP_get, writerWP_set]
          refine (writerWP_getNode_known L n c _ ?_ _).mpr ?_
          · simp only [List.lookup_append, hlk]; rfl
          rw [putNode, writerWP_modify]
          refine ⟨rfl, rfl, l, hl1, hl2, hl3, hl4, ?_⟩
          intro x
          show (upsert _ L _).lookup x = _
          rw [lookup_upsert]
          by_cases hxL : x = L
          · simp [hxL]
          · simp only [hxL, ↓reduceIte, List.lookup_append]
            by_cases hxy : x = w.next
            · subst hxy; rw [hny]; simp [List.lookup]
            · simp only [hxy, ↓reduceIte]
              cases h : w.nodes.lookup x with
              | some m => rfl
              | none =>
                show (none : Option KNode).or ([(w.next, { leaf := n.leaf, ks := l.ks })].lookup x) = none
                rw [lookup_cons_ne _ _ _ _ hxy]; rfl

/-- `appendKlongs` at the space root L (depth 0), not made by the transaction, without room
for ins or compacting, with its last version within a split's bound when it has no room:
the time split of `writerWP_handleFullWith_rootTimeSplit_ins`. -/
theorem writerWP_appendKlongs_rootTime (L : NodeId) (n : KNode) (ins : List (Nat × NodeId))
    (c : Ctx) (w : W)
    (hlk : w.nodes.lookup L = some n) (hfirst : n.firstTime ≠ some c.i)
    (hLn : L < w.next) (hny : w.nodes.lookup w.next = none)
    (hfull : n.size + ins.length + 1 ≤ c.p.M →
      deadOver c.p (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) n) = true)
    (htime : c.p.M < n.size + ins.length + 1 → (n.lastVersion c.i).size ≤ c.p.splitAbove) :
    WriterWP (appendKlongs 0 L ins) c w (fun _ w' =>
      w'.taken = w.taken ∧ w'.top.rootKey = w.next ∧ ∃ out : KNode,
        out.leaf = n.leaf ∧ klongsWf out.ks = true ∧ (∀ s, Klong.time s ∈ out.ks → s ≤ c.i) ∧
        (∀ q, out.live.lookup q = ins.foldl (pairLookupStep q) (n.live.lookup q)) ∧
        ∀ x, w'.nodes.lookup x =
          if x = L then some (n.toPrev (c.i - 1))
          else if x = w.next then some ⟨n.leaf, out.ks⟩ else w.nodes.lookup x) := by
  rw [appendKlongs_step_dead]
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known _ _ c w hlk]
  by_cases hsz : n.size + ins.length + 1 > c.p.M
  · simp only [hsz, ↓reduceIte]
    have h2 := htime hsz
    exact writerWP_handleFullWith_rootTimeSplit_ins _ L n ins false c w hlk hfirst
      (by simp only [Bool.not_false, Bool.true_and, decide_eq_false_iff_not, gt_iff_lt]; omega)
      hLn hny
  · have hd := hfull (by omega)
    simp only [hsz, hd, ↓reduceIte]
    exact writerWP_handleFullWith_rootTimeSplit_ins _ L n ins true c w hlk hfirst
      (by simp) hLn hny

/-- The space root L, a segment leaf not made by the transaction, gets p's copy y by
p's klong k1 and splits in time (`split.time2`): the new space root, its last version
with that klong, is a leaf whose search of k1 names y; L is no longer the root, the
other nodes and the taken set are kept. What `descendToHeight_topSeg_leafRoot` takes. -/
theorem writerWP_appendKlongs_rootTimeHole (L : NodeId) (n : KNode) (k1 : Nat) (y : NodeId)
    (c : Ctx) (w : W)
    (hlk : w.nodes.lookup L = some n) (hfirst : n.firstTime ≠ some c.i)
    (hLn : L < w.next) (hny : w.nodes.lookup w.next = none)
    (hfull : n.size + 2 ≤ c.p.M → deadOver c.p (n.add c.i (.key k1 y)) = true)
    (htime : c.p.M < n.size + 2 → (n.lastVersion c.i).size ≤ c.p.splitAbove) :
    WriterWP (appendKlongs 0 L [(k1, y)]) c w (fun _ w' =>
      w'.taken = w.taken ∧ w'.top.rootKey = w.next ∧
      (∀ z, z ≠ L → z ≠ w.next → w'.nodes.lookup z = w.nodes.lookup z) ∧
      ∃ qn', rdN c w' w'.top.rootKey = some qn' ∧ qn'.leaf = n.leaf ∧
        ∃ fd', qn'.searchEq c.i k1 = some fd' ∧ fd'.y = y) := by
  refine writerWP_mono (writerWP_appendKlongs_rootTime L n [(k1, y)] c w hlk hfirst hLn hny
    (fun h => hfull (by simpa using h)) (fun h => htime (by simpa using h))) ?_
  rintro _ w' ⟨ht, hr, out, hl1, hl2, hl3, hl4, hlook⟩
  have hL1 : L ≠ w.next := by omega
  have hq : (⟨n.leaf, out.ks⟩ : KNode) = out := by rw [← hl1]
  refine ⟨ht, hr, fun z h1 h2 => by rw [hlook z]; simp [h1, h2], out, ?_, hl1, ?_⟩
  · rw [hr]
    apply rdN_of_lookup
    rw [hlook w.next]
    simp [Ne.symm hL1, hq]
  · have hs := KNode.searchEq_live out c.i hl2 hl3 k1
    rw [hl4 k1] at hs
    simp only [List.foldl_cons, List.foldl_nil, pairLookupStep, beq_self_eq_true, ↓reduceIte] at hs
    obtain ⟨fd', hfd', hfy⟩ := Option.map_eq_some_iff.mp hs
    exact ⟨fd', hfd', hfy⟩

end SIS.Tree
