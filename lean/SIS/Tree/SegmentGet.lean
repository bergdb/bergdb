import SIS.Tree.SegmentRange
import SIS.Tree.SearchEqProof

namespace SIS.Tree

open SIS SIS.Check

theorem KNode.liveAt_keys_nodup (n : KNode) (t : Time) :
    ((n.liveAt t).map Prod.fst).Nodup := by
  rw [n.liveAt_eq_live_prefix]
  exact KNode.live_keys_nodup _

/-- An inner search selects exactly the child whose interval contains the
query, including the selected pointer and its separator. -/
theorem KNode.searchLte_child (n : KNode) (t : Time) (hi : Option Nat)
    (q : Nat × NodeId) (b : Option Nat) (hq : (q,b) ∈ childBounds (n.liveAt t) hi)
    (cv : Nat) (hlo : q.1 ≤ cv) (hhi : UpperBound b cv) :
    ∃ fd, n.searchLte t cv = some fd ∧ fd.c = q.1 ∧ fd.y = q.2 := by
  have hmem := childBounds_fst _ _ _ _ hq
  have hspec := n.searchLte_spec t cv
  cases hf : n.searchLte t cv with
  | none =>
    have hno := (hspec.2.mp hf) q hmem
    simp only [decide_eq_false_iff_not] at hno
    omega
  | some fd =>
    obtain ⟨hfd,hle,hmax⟩ := hspec.1 fd hf
    have hqle := hmax q hmem (by simp; omega)
    have hfdle : fd.c ≤ q.1 := childBounds_dominates (n.liveAt t) hi
      (n.liveAt_order t) q b hq cv hhi (fd.c,fd.y) hfd (by
        simp only [decide_eq_true_eq] at hle
        omega)
    have heq : fd.c = q.1 := by
      simp only [decide_eq_true_eq] at hqle
      omega
    have hlookup := lookup_some_of_mem (n.liveAt_keys_nodup t) hmem
    have hlookup' := lookup_some_of_mem (n.liveAt_keys_nodup t) hfd
    rw [heq,hlookup] at hlookup'
    exact ⟨fd,rfl,heq,(Option.some.inj hlookup').symm⟩

end SIS.Tree
