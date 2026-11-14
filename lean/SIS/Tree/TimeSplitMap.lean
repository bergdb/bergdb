import SIS.Tree.PairReplace
import SIS.Tree.NodeMap
import SIS.Tree.MergeProtectedDelete
import SIS.Tree.DeleteCount
import SIS.Tree.HistoricalPrefix

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

end SIS.Tree
