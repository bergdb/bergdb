import SIS.Tree.PairReplace
import SIS.Tree.WriterNodeMap

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- The actual time-split loop implements ordered overwrites of the input
map, even if its inserted compare values repeat. Its physical output remains
a one-time list with one entry per compare value. -/
theorem writerWP_replaceOrAdd_map (leaf : Bool) (pairs ins : List (Nat × NodeId))
    (hn : (pairs.map Prod.fst).Nodup) (c : Ctx) (w : W) :
    WriterWP (replaceOrAdd ⟨leaf, newKlongs c.i pairs⟩ ins) c w (fun out v =>
      out.leaf = leaf ∧
      (∃ more, out.ks = newKlongs c.i more ∧ (more.map Prod.fst).Nodup) ∧
      (∀ q, out.live.lookup q = ins.foldl (pairLookupStep q) (pairs.lookup q)) ∧ v = w) := by
  unfold replaceOrAdd
  simp only [writerWP_bind, writerWP_read]
  induction ins generalizing pairs with
  | nil =>
    simp only [List.foldlM_nil, writerWP_pure]
    refine ⟨trivial, ⟨pairs, rfl, hn⟩, ?_, trivial⟩
    intro q
    exact KNode.newKlongs_live_lookup leaf c.i pairs hn q
  | cons pair ins ih =>
    rcases pair with ⟨cv,y⟩
    rw [List.foldlM_cons, writerWP_bind, replaceKlong_newKlongs]
    cases hr : replacePairFirst pairs cv y with
    | none =>
      simp only [hr, Option.map_none, writerWP_pure, KNode.newKlongs_add_key]
      have hnone := replacePairFirst_none pairs cv y hr
      have hnd := pair_append_new_nodup pairs cv y hn hnone
      refine writerWP_mono (ih (pairs ++ [(cv,y)]) hnd) ?_
      rintro out v ⟨hleaf, hshape, hmap, hv⟩
      refine ⟨hleaf, hshape, ?_, hv⟩
      intro q
      rw [hmap, List.foldl_cons, pairLookupStep, pair_append_new_lookup pairs cv q y hnone]
    | some more =>
      simp only [hr, Option.map_some, writerWP_pure]
      obtain ⟨hkeys, hlookup⟩ := replacePairFirst_some pairs more cv y hr
      have hnd : (more.map Prod.fst).Nodup := by rw [hkeys]; exact hn
      refine writerWP_mono (ih more hnd) ?_
      rintro out v ⟨hleaf, hshape, hmap, hv⟩
      refine ⟨hleaf, hshape, ?_, hv⟩
      intro q
      rw [hmap, List.foldl_cons, pairLookupStep, hlookup q]

theorem writerWP_replaceOrAdd_normalized_map (n : KNode) (del : List Nat)
    (ins : List (Nat × NodeId)) (c : Ctx) (w : W) :
    WriterWP (replaceOrAdd (n.lastVersionGivenDel c.i del) ins) c w (fun out v =>
      out.leaf = n.leaf ∧
      (∀ q, out.live.lookup q = ins.foldl (pairLookupStep q) (keyLookup n.ks del q)) ∧ v = w) := by
  obtain ⟨pairs, hks, horder⟩ := n.lastVersionGivenDel_order c.i del
  have hnd : (pairs.map Prod.fst).Nodup := List.pairwise_map.mpr
    (horder.imp (by intro a b hab; omega))
  have hleaf : (n.lastVersionGivenDel c.i del).leaf = n.leaf := rfl
  have he : n.lastVersionGivenDel c.i del = ⟨n.leaf, newKlongs c.i pairs⟩ := by
    cases hout : n.lastVersionGivenDel c.i del
    simp_all [newKlongs]
  have hlookup : ∀ q, pairs.lookup q = keyLookup n.ks del q := by
    intro q
    have hh := n.lastVersionGivenDel_pairs_lookup c.i del q
    simpa [hks, List.filterMap_map, Function.comp_def] using hh
  rw [he]
  refine writerWP_mono (writerWP_replaceOrAdd_map n.leaf pairs ins hnd c w) ?_
  rintro out v ⟨hleaf, _, hmap, hv⟩
  refine ⟨hleaf, ?_, hv⟩
  intro q
  rw [hmap, hlookup]

/-- A time replacement of a current-transaction node preserves its guarded
id and implements the complete inserted map in place. The time-route premise
includes dead compaction. -/
theorem writerWP_handleFullWith_time_new_map (b : NodeGuard)
    (up : NodeId → List (Nat × NodeId) → M Unit) (depth : Nat)
    (leaf : Bool) (pairs ins : List (Nat × NodeId)) (compact : Bool)
    (c : Ctx) (w : W) (hw : GuardHeld b w) (ht : b.node.firstTime = some c.i)
    (hn : (pairs.map Prod.fst).Nodup)
    (htime : compact = true ∨ (⟨leaf, newKlongs c.i pairs⟩ : KNode).size ≤ c.p.splitAbove) :
    WriterWP (handleFullWith up depth b.id ins ⟨leaf, newKlongs c.i pairs⟩ compact) c w
      (fun _ v => ∃ after, GuardHeld {b with node := after} v ∧
        ∀ q, after.live.lookup q = ins.foldl (pairLookupStep q) (pairs.lookup q)) := by
  have hflag : (!compact && decide ((⟨leaf, newKlongs c.i pairs⟩ : KNode).size > c.p.splitAbove)) = false := by
    rcases htime with hc | hs
    · simp [hc]
    · simp [show ¬ (⟨leaf, newKlongs c.i pairs⟩ : KNode).size > c.p.splitAbove from by omega]
  unfold handleFullWith
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known b.id b.node c w hw.1]
  refine writerWP_mono (guard_ghOf b b.id c w hw) ?_
  intro gh v hv
  simp only [ht, BEq.rfl]
  unfold parentAt pathNode
  repeat' first
    | wpSimplify
    | simp only [hflag, Bool.false_eq_true, Bool.not_true, note, ↓reduceIte]
    | kgUse b using (guard_getNode b _)
    | ((with_unfolding_none guard_target = WriterWP (replaceOrAdd _ _) _ _ _)
       refine writerWP_mono (writerWP_replaceOrAdd_map leaf pairs ins hn c _) ?_
       rintro out state ⟨hleaf, hshape, hmap, heq⟩
       subst state)
    | ((with_unfolding_none guard_target = WriterWP (putNode _ _) _ _ _)
       refine writerWP_mono (writerWP_putNode_guard_same b _ _ _ (by kgState)) ?_
       intro result state hguard)
    | (refine ⟨_, hguard, ?_⟩; simpa only [KNode.live_with_leaf] using hmap)
    | exact writerWP_throw _ _ _ _
    | split

end SIS.Tree
