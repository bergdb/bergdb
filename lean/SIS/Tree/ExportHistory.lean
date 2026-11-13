import SIS.Tree.WriterHistory
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

/-- Node-local history application is unaffected by export's final sorting. -/
theorem changesOf_addsFor (i : Time) (w : W) (x : NodeId) :
    addsFor (changesOf i w) i x =
      ((keyAdditions i w ++ valueAdditions w ++ topAdditions w).filter
        (fun a => a.1 == x)).map (fun a => ⟨i, a.2⟩) := by
  rw [addsFor, changesOf_adds, filter_id_mergeSort]

/-- Filtering a unique cache id selects precisely that node's physical
entries, unless it was taken back. -/
theorem keyAdditions_at (i : Time) (w : W) (x : NodeId) (n : KNode)
    (hunique : (w.nodes.map Prod.fst).Nodup) (hn : (x, n) ∈ w.nodes)
    (ht : w.taken.contains x = false) :
    (keyAdditions i w).filter (fun a => a.1 == x) =
      (currentEntries i n).map (fun e => (x, e.val)) := by
  unfold keyAdditions
  have general : ∀ ns : List (NodeId × KNode),
      (ns.map Prod.fst).Nodup → (x, n) ∈ ns →
      ((ns.filter (fun q => !w.taken.contains q.1)).flatMap (fun q =>
        (currentEntries i q.2).map (fun e => (q.1, e.val)))).filter
          (fun a => a.1 == x) = (currentEntries i n).map (fun e => (x, e.val)) := by
    intro ns
    induction ns with
    | nil => intro _ h; cases h
    | cons q ns ih =>
      intro hu hm
      have hu' := List.nodup_cons.mp hu
      rcases List.mem_cons.mp hm with he | hm
      · cases he
        have hnone : ∀ q ∈ ns, q.1 ≠ x := by
          intro q hq hx
          apply hu'.1
          exact List.mem_map.mpr ⟨q, hq, hx⟩
        have hrest :
            (((ns.filter (fun q => !w.taken.contains q.1)).flatMap (fun q =>
              (currentEntries i q.2).map (fun e => (q.1, e.val)))).filter
                (fun a => a.1 == x)) = [] := by
          apply List.filter_eq_nil_iff.mpr
          intro a ha
          obtain ⟨q, hq, ha⟩ := List.mem_flatMap.mp ha
          obtain ⟨e, _, rfl⟩ := List.mem_map.mp ha
          simp [hnone q (List.mem_filter.mp hq).1]
        simp only [List.filter_cons, ht, Bool.not_false, ↓reduceIte,
          List.flatMap_cons, List.filter_append, hrest, List.append_nil]
        simp only [List.filter_map, Function.comp_def, beq_self_eq_true]
        rw [List.filter_eq_self.mpr (by intro a ha; rfl)]
      · have hqx : q.1 ≠ x := by
          intro hx
          apply hu'.1
          exact List.mem_map.mpr ⟨(x,n), hm, hx.symm⟩
        have hdrop : ((currentEntries i q.2).map (fun e => (q.1, e.val))).filter
            (fun a => a.1 == x) = [] := by
          simp [List.filter_map, hqx]
        cases htake : w.taken.contains q.1 <;>
          simp only [List.filter_cons, htake, Bool.not_true, Bool.not_false,
            Bool.false_eq_true, ↓reduceIte, List.flatMap_cons,
            List.filter_append, hdrop, List.nil_append, ih hu'.2 hm]
  exact general w.nodes hunique hn

/-- A retained key id has exactly its cached transaction-time history.
The explicit separation premises exclude value and top-node additions. -/
theorem changesOf_key_addsFor (i : Time) (w : W) (x : NodeId) (n : KNode)
    (hunique : (w.nodes.map Prod.fst).Nodup) (hn : (x, n) ∈ w.nodes)
    (ht : w.taken.contains x = false)
    (hv : ∀ q ∈ w.vals, q.1 ≠ x) (hr : x ≠ root) (hz : x ≠ w.top.id) :
    addsFor (changesOf i w) i x = currentEntries i n := by
  have hval : (valueAdditions w).filter (fun a => a.1 == x) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro a ha
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ha
    simp [hv q hq]
  have htop : (topAdditions w).filter (fun a => a.1 == x) = [] := by
    unfold topAdditions
    split
    · have hskip : (w.top.skips.map (fun q => (w.top.id, BVal.skip q.1 q.2))).filter
          (fun a => a.1 == x) = [] := by
        simp [List.filter_map, Ne.symm hz]
      simp [Ne.symm hr, Ne.symm hz, hskip]
    · rfl
  rw [changesOf_addsFor, List.filter_append, List.filter_append,
    keyAdditions_at i w x n hunique hn ht, hval, htop]
  simp only [List.append_nil, List.map_map]
  calc
    _ = (currentEntries i n).map (fun e => e) := by
      apply List.map_congr_left
      intro e he
      have ht' : e.time = i := by simpa using (List.mem_filter.mp he).2
      cases e
      simp_all
    _ = _ := List.map_id' _

/-- Exact reconstruction of a retained old key node, with the temporal
cache correspondence stated explicitly. No invariant of the result is used. -/
theorem apply_changesOf_cached (P : Struct BVal) (i : Time) (w : W)
    (x : NodeId) (old : Node BVal) (n : KNode) (hold : P.get? x = some old)
    (hunique : (w.nodes.map Prod.fst).Nodup) (hn : (x, n) ∈ w.nodes)
    (ht : w.taken.contains x = false)
    (hv : ∀ q ∈ w.vals, q.1 ≠ x) (hr : x ≠ root) (hz : x ≠ w.top.id)
    (hh : old.hist ++ currentEntries i n = entriesOf n.ks) :
    (P.apply i (changesOf i w)).get? x = some {old with hist := entriesOf n.ks} := by
  rw [get?_apply_of_get? hold,
    changesOf_key_addsFor i w x n hunique hn ht hv hr hz, hh]

/-- Under exact temporal correspondence, exported old nodes inherit the
physical history and round trip of the complete cached output. -/
theorem apply_changesOf_cached_klongs (P : Struct BVal) (i : Time) (w : W)
    (x : NodeId) (old : Node BVal) (n : KNode) (hold : P.get? x = some old)
    (hunique : (w.nodes.map Prod.fst).Nodup) (hn : (x, n) ∈ w.nodes)
    (ht : w.taken.contains x = false)
    (hv : ∀ q ∈ w.vals, q.1 ≠ x) (hr : x ≠ root) (hz : x ≠ w.top.id)
    (hh : old.hist ++ currentEntries i n = entriesOf n.ks)
    (hw : WriterKlongsWf w) :
    ∃ after, (P.apply i (changesOf i w)).get? x = some after ∧
      klongsOf after.hist = n.ks ∧ klongsWf (klongsOf after.hist) = true := by
  have h := hw (x,n) hn
  refine ⟨{old with hist := entriesOf n.ks},
    apply_changesOf_cached P i w x old n hold hunique hn ht hv hr hz hh, ?_, ?_⟩
  · exact klongsRoundTrip n.ks h
  · simpa only [klongsRoundTrip n.ks h] using h

end SIS.Tree
