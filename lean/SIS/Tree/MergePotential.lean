import SIS.Tree.DeleteCount

namespace SIS.Tree

open SIS SIS.Check

/-- A nonroot node has one unit for its existence and one per missing live
entry below m. Roots have no such units. -/
def fillPotential (m cnt : Nat) : Nat := 1 + (m-cnt)

/-- The replacement potential of the current reachable key nodes. -/
def treeFillPotential (p : Params) (P : Struct BVal) (t : Time) : Nat :=
  ((nodesRootsAt p P t).map (fun q => if q.2 then 0 else
    ((keyNodeAt p P q.1).map (fun n => fillPotential p.mergeBelow (n.liveAt t).length)).getD 0)).sum

theorem fillPotential_full (m cnt : Nat) (h : m ≤ cnt) : fillPotential m cnt = 1 := by
  simp [fillPotential,Nat.sub_eq_zero_of_le h]

theorem fillPotential_delete (m before after : Nat) (h : before ≤ after+1) :
    fillPotential m after ≤ fillPotential m before + 1 := by
  unfold fillPotential
  omega

theorem fillPotential_put (m before after : Nat) (h : before ≤ after) :
    fillPotential m after ≤ fillPotential m before := by
  unfold fillPotential
  omega

theorem fillPotential_normalized_delete (p : Params) (n : KNode) (t : Time) (cv : Nat) :
    fillPotential p.mergeBelow
        (n.lastVersionGivenDel t (bitsUnion n.lastBitmap (n.bitsOf cv))).cnt ≤
      fillPotential p.mergeBelow n.cnt + 1 := by
  exact fillPotential_delete _ _ _ (n.delete_count_bounds t cv).2

theorem fillPotential_append_delete (p : Params) (n : KNode) (t : Time) (cv : Nat) :
    fillPotential p.mergeBelow
        (n.add t (.del (bitsUnion n.lastBitmap (n.bitsOf cv)))).cnt ≤
      fillPotential p.mergeBelow n.cnt + 1 := by
  have hc := n.add_delete_count_exact t cv
  apply fillPotential_delete
  split at hc <;> omega

/-- Replacing a segment root by two full children introduces at most two
units. An internal split also removes the old node's units. -/
theorem fillPotential_split (m first second : Nat) (hf : m ≤ first) (hs : m ≤ second) :
    fillPotential m first + fillPotential m second = 2 := by
  rw [fillPotential_full _ _ hf,fillPotential_full _ _ hs]

/-- One-output merges pay for their own merge and the parent's possible
one-entry loss. -/
theorem fillPotential_merge_one (m small sibling out parent parent' : Nat)
    (hsmall : small < m) (hsibling : m ≤ sibling) (hout : m ≤ out)
    (hparent : parent ≤ parent'+1) :
    fillPotential m out + fillPotential m parent' + 1 ≤
      fillPotential m small + fillPotential m sibling + fillPotential m parent := by
  have hp := fillPotential_delete m parent parent' hparent
  rw [fillPotential_full _ _ hsibling,fillPotential_full _ _ hout]
  unfold fillPotential at *
  omega

/-- Two-output merges preserve the parent's live count. Their two new
existence units are paid by the two old nodes and the deficient node's unit. -/
theorem fillPotential_merge_two (m small sibling first second parent parent' : Nat)
    (hsmall : small < m) (hsibling : m ≤ sibling)
    (hfirst : m ≤ first) (hsecond : m ≤ second) (hparent : parent ≤ parent') :
    fillPotential m first + fillPotential m second + fillPotential m parent' + 1 ≤
      fillPotential m small + fillPotential m sibling + fillPotential m parent := by
  have hp := fillPotential_put m parent parent' hparent
  rw [fillPotential_full _ _ hsibling,fillPotential_full _ _ hfirst,
    fillPotential_full _ _ hsecond]
  unfold fillPotential at *
  omega

/-- The potential suggested in TP33's comment need not decrease on every
merge under MergeParamsOK: at m=2,c=3, sizes 1 and 3 merge into 2 and 2. -/
theorem commentPotential_two_output_witness :
    MergeParamsOK ({M := 8,G := 0,H := 1,mergeBelow := 2,mergeMax := 3,splitAbove := 4} : Params) ∧
    mergeKlongs false 3 64 [(0,1)] [(64,2),(128,3),(192,4)] =
      ([(0,1),(64,2)],some ([(128,3),(192,4)],128)) ∧
    (3-1 : Nat)+(3-3) = (3-2)+(3-2) ∧
    ¬ (3-2 : Nat)+(3-2)+1 ≤ (3-1)+(3-3) := by
  unfold MergeParamsOK
  decide +kernel

/-- A run annotated with a nonnegative potential. Each step pays its merges
from its deletes, twice its splits, and the decrease in potential. -/
def PotentialCosts : List (Nat × Nat × Nat) → Nat → Prop
  | [], _ => True
  | q :: qs, before => ∃ after,
      after + q.1 ≤ before + q.2.1 + 2*q.2.2 ∧ PotentialCosts qs after

theorem potentialCosts_sum (costs : List (Nat × Nat × Nat)) (initial : Nat)
    (h : PotentialCosts costs initial) :
    (costs.map (·.1)).sum ≤ initial + (costs.map (·.2.1)).sum +
      2*(costs.map (·.2.2)).sum := by
  induction costs generalizing initial with
  | nil => simp
  | cons q qs ih =>
    obtain ⟨after,hstep,hrest⟩ := h
    have ht := ih after hrest
    simp only [List.map_cons,List.sum_cons,Nat.mul_add]
    omega

/-- TP33 follows from an annotation of the actual run costs. Constructing
that annotation from the writer remains a separate obligation. -/
theorem mergeAmortized_of_potential (p : Params)
    (h : MergeParamsOK p → ∀ ts, Within p ts → PotentialCosts (runCosts p ts) 0) :
    MergeAmortized p := by
  intro hp ts hts
  have hs := potentialCosts_sum (runCosts p ts) 0 (h hp ts hts)
  simpa only [List.sum_eq_foldl,Nat.zero_add] using hs

end SIS.Tree
