import SIS.Tree.WriterKlongOps
import SIS.Tree.InvInit
import SIS.Tree.RunPrefix

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- Sorting additions by node id keeps the physical order within each node. -/
theorem filter_id_mergeSort {α : Type} (xs : List (NodeId × α)) (x : NodeId) :
    (xs.mergeSort (fun a b => decide (a.1 ≤ b.1))).filter (fun a => a.1 == x) =
      xs.filter (fun a => a.1 == x) := by
  have hs : (xs.filter (fun a => a.1 == x)).Pairwise
      (fun a b => decide (a.1 ≤ b.1)) := by
    apply List.pairwise_of_forall_mem_list
    intro a ha b hb
    have ha' : a.1 = x := by simpa using (List.mem_filter.mp ha).2
    have hb' : b.1 = x := by simpa using (List.mem_filter.mp hb).2
    simp [ha', hb']
  have hsub := List.sublist_mergeSort
    (le := fun a b : NodeId × α => decide (a.1 ≤ b.1))
    (by intro a b c hab hbc; simp only [decide_eq_true_eq] at *; omega)
    (by intro a b; simp only [Bool.or_eq_true, decide_eq_true_eq]; omega)
    hs (List.filter_sublist (l := xs) (p := fun a => a.1 == x))
  have hf := hsub.filter (fun a => a.1 == x)
  simp only [List.filter_filter, Bool.and_self] at hf
  have hp := (List.mergeSort_perm xs (fun a b => decide (a.1 ≤ b.1))).filter
    (fun a => a.1 == x)
  exact (hf.eq_of_length hp.length_eq.symm).symm

/-- The transaction-time entries of a cached key node, in physical order. -/
def currentEntries (i : Time) (n : KNode) : History BVal :=
  (entriesOf n.ks).filter (fun e => e.time == i)

def keyAdditions (i : Time) (w : W) : List (NodeId × BVal) :=
  (w.nodes.filter (fun q => !w.taken.contains q.1)).flatMap (fun q =>
    (currentEntries i q.2).map (fun e => (q.1, e.val)))

def valueAdditions (w : W) : List (NodeId × BVal) :=
  w.vals.map (fun q => (q.1, BVal.data q.2))

def topAdditions (w : W) : List (NodeId × BVal) :=
  if w.newTop then
    (root, BVal.top w.top.id) :: (w.top.id, BVal.rootKey w.top.rootKey) ::
      w.top.skips.map (fun q => (w.top.id, BVal.skip q.1 q.2))
  else []

/-- Exact additions of each origin, before the stable grouping by node id. -/
theorem changesOf_adds (i : Time) (w : W) :
    (changesOf i w).adds =
      (keyAdditions i w ++ valueAdditions w ++ topAdditions w).mergeSort
        (fun a b => decide (a.1 ≤ b.1)) := rfl

end SIS.Tree
