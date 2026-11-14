/-
TP33 (`MergeAmortized`, CB3 of bergdb 024-11) by a simpler potential than
024-11's: the number of reachable key nodes that are not the root of their
segment tree (bergdb 024-22, section 6). A merge into one node removes one such
node; a merge into two nodes leaves the count and ends its delete's loop (at
most one a delete that deletes); a space split adds at most two (the halves,
and a new root above a root); nothing else adds one (a time split replaces a
node, a new segment tree starts with its root, the upward unlink and root
collapse remove nodes). The potential needs no fill (V1).

Proved here: TP33 follows from the one-transaction step of this potential
(`NodeCountStep`), by the same telescoping as `RunPotential.lean`, for any
potential that is zero on R(0); and, since a transaction's merges into two
nodes are at most its deletes (`execW_twoMerges_le_deletes`), from the step
of the merges into one node alone (`OneMergeStep`): the count of non-root nodes
falls by one at each, and space splits add at most two each. The step itself is
a statement on the writer and the trees before and after the transaction; it is
not proved here.
-/
import SIS.Tree.RunPotential
import SIS.Tree.MergeTwoCount

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- The reachable key nodes at time t that are not the root of their segment
tree (`nodesRootsAt`, the walk's order). -/
def nonRootCount (p : Params) (P : Struct BVal) (t : Time) : Nat :=
  (nodesRootsAt p P t).countP (fun q => !q.2)

theorem nonRootCount_init (p : Params) (t : Time) :
    nonRootCount p (initStruct p) t = 0 := by
  simp [nonRootCount, nodesRootsAt_init]

/-- The one-transaction step of a potential on the trees of a run: a
transaction's merges are paid by its deletes that delete, twice its space
splits, and the drop of the potential from P@(i-1) to P@i. -/
def PotentialStep (p : Params) (pot : Struct BVal → Time → Nat) : Prop :=
  ∀ ts tx, Within p (ts ++ [tx]) → ∀ noops w,
    execW p tx (ts.length + 1) (view (treeSpec p) (treeRun p ts) ts.length) = .ok (noops,w) →
    pot (treeRun p (ts ++ [tx])) (ts.length + 1) + w.merges ≤
      pot (treeRun p ts) ts.length + deletesOf tx noops + 2 * w.spaceSplits

/-- Telescoping over the actual successful transactions of a run, for any
potential that is zero on R(0); the final potential stays in the conclusion. -/
theorem potential_run_costs (p : Params) (pot : Struct BVal → Time → Nat)
    (h0 : pot (initStruct p) 0 = 0) (hstep : PotentialStep p pot)
    (ts : List Tx) (hw : Within p ts) :
    pot (treeRun p ts) ts.length + ((runCosts p ts).map (·.1)).sum ≤
      ((runCosts p ts).map (·.2.1)).sum + 2 * ((runCosts p ts).map (·.2.2)).sum := by
  have hf : ∀ revts : List Tx, Within p revts.reverse →
      pot (treeRun p revts.reverse) revts.reverse.length +
        ((runCosts p revts.reverse).map (·.1)).sum ≤
        ((runCosts p revts.reverse).map (·.2.1)).sum +
          2 * ((runCosts p revts.reverse).map (·.2.2)).sum := by
    intro revts
    induction revts with
    | nil =>
      intro _
      simp only [List.reverse_nil, treeRun, List.zipIdx_nil, List.foldl_nil, List.length_nil,
        h0, runCosts, List.filterMap_nil, List.map_nil, List.sum_nil]
      omega
    | cons tx revts ih =>
      intro hwithin
      simp only [List.reverse_cons] at hwithin ⊢
      have hprefix := within_snoc_prefix p revts.reverse tx hwithin
      have hcost := ih hprefix
      obtain ⟨noops, w, he⟩ := execW_success_of_within_snoc p revts.reverse tx hwithin
      have hlocal := hstep revts.reverse tx hwithin noops w he
      rw [runCosts_snoc, he]
      simp only [List.map_append, List.map_cons, List.map_nil, List.sum_append,
        List.sum_cons, List.sum_nil, Nat.add_zero, List.length_append, List.length_singleton]
      omega
  simpa only [List.reverse_reverse] using hf ts.reverse (by simpa using hw)

/-- TP33 from the step of any potential that is zero on R(0). -/
theorem mergeAmortized_of_potentialStep (p : Params) (pot : Struct BVal → Time → Nat)
    (h0 : pot (initStruct p) 0 = 0) (hstep : MergeParamsOK p → PotentialStep p pot) :
    MergeAmortized p := by
  intro hp ts hw
  have hh := potential_run_costs p pot h0 (hstep hp) ts hw
  simp only [List.sum_eq_foldl] at hh
  exact Nat.le_trans (Nat.le_add_left _ _) hh

/-- TP33's step with the count of non-root nodes as the potential: the node
count of P@i and the transaction's merges are at most the node count of
P@(i-1), its deletes that delete, and twice its space splits. -/
def NodeCountStep (p : Params) : Prop := PotentialStep p (nonRootCount p)

/-- TP33 (`MergeAmortized`) from the node-count step, without fill. -/
theorem mergeAmortized_of_nodeCountStep (p : Params)
    (hstep : MergeParamsOK p → NodeCountStep p) : MergeAmortized p :=
  mergeAmortized_of_potentialStep p (nonRootCount p) (nonRootCount_init p 0) hstep

/-- TP33's step for the merges into one node: the node count of P@i and the
transaction's merges into one node (its merges but those into two,
`twoNotes`) are at most the node count of P@(i-1) and twice its space splits.
The deletes do not appear: they pay for the merges into two nodes. -/
def OneMergeStep (p : Params) : Prop :=
  ∀ ts tx, Within p (ts ++ [tx]) → ∀ noops w,
    execW p tx (ts.length + 1) (view (treeSpec p) (treeRun p ts) ts.length) = .ok (noops,w) →
    nonRootCount p (treeRun p (ts ++ [tx])) (ts.length + 1) + (w.merges - twoNotes w) ≤
      nonRootCount p (treeRun p ts) ts.length + 2 * w.spaceSplits

/-- The step of the merges into one node gives the node-count step: the merges
into two nodes are at most the deletes that deleted. -/
theorem nodeCountStep_of_oneMergeStep (p : Params) (h : OneMergeStep p) : NodeCountStep p := by
  intro ts tx hw noops w he
  have h1 := h ts tx hw noops w he
  have h2 := execW_twoMerges_le_deletes p tx (ts.length + 1) _ noops w he
  have h3 : w.merges ≤ (w.merges - twoNotes w) + twoNotes w := by omega
  omega

/-- TP33 (`MergeAmortized`) from the step of the merges into one node. -/
theorem mergeAmortized_of_oneMergeStep (p : Params)
    (hstep : MergeParamsOK p → OneMergeStep p) : MergeAmortized p :=
  mergeAmortized_of_nodeCountStep p (fun hp => nodeCountStep_of_oneMergeStep p (hstep hp))

end SIS.Tree
