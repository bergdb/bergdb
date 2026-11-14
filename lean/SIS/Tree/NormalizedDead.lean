import SIS.Tree.TimeSplitMap
import SIS.Tree.WriterKlongOps

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- Distinct compare values for any two physical key klongs. -/
def DifferentKeyCvs (a b : Klong) : Prop :=
  match a, b with
  | .key cv _, .key cv' _ => cv ≠ cv'
  | _, _ => True

/-- With no deletion bits and no repeated physical compare values, the
dead-klong counter is exactly zero. No time or tree premises are needed. -/
theorem KNode.deadCount_zero_of_distinct (n : KNode)
    (hb : n.lastBitmap = []) (hp : n.ks.Pairwise DifferentKeyCvs) : n.deadCount = 0 := by
  unfold KNode.deadCount
  rw [hb]
  apply List.length_eq_zero_iff.mpr
  apply List.filter_eq_nil_iff.mpr
  intro q hq
  rcases q with ⟨k, i⟩
  have hk := List.mem_zipIdx_iff_getElem?.mp hq
  cases k with
  | time t => simp
  | del bits => simp
  | key cv y =>
    intro hdead
    simp only [List.contains_nil, Bool.false_or] at hdead
    obtain ⟨later, hlater, heq⟩ := List.any_eq_true.mp hdead
    have hi := List.getElem?_eq_some_iff.mp hk
    obtain ⟨j, hj, hget⟩ := List.mem_drop_iff_getElem.mp hlater
    have hij : i < i + 1 + j := by omega
    have hrel := hp.rel_getElem_of_lt hi.1 (by omega : i + 1 + j < n.ks.length) hij
    rw [hi.2, hget] at hrel
    cases later with
    | time t => simp at heq
    | del bits => simp at heq
    | key cv' z =>
      change cv ≠ cv' at hrel
      have he : cv' = cv := by simpa only [beq_iff_eq] using heq
      exact hrel he.symm

theorem newKlongs_different (t : Time) (pairs : List (Nat × NodeId))
    (hn : (pairs.map Prod.fst).Nodup) :
    (newKlongs t pairs).Pairwise DifferentKeyCvs := by
  apply List.pairwise_cons.mpr
  refine ⟨by intro k hk; trivial, ?_⟩
  have hp : pairs.Pairwise (fun a b => a.1 ≠ b.1) := List.pairwise_map.mp hn
  exact (List.pairwise_map (f := fun q : Nat × NodeId => Klong.key q.1 q.2)).mpr hp

theorem KNode.newKlongs_deadCount (leaf : Bool) (t : Time) (pairs : List (Nat × NodeId))
    (hn : (pairs.map Prod.fst).Nodup) :
    (⟨leaf, newKlongs t pairs⟩ : KNode).deadCount = 0 :=
  KNode.deadCount_zero_of_distinct _ (lastBitmapOf_newKlongs t pairs)
    (newKlongs_different t pairs hn)

/-- Normalization removes every dead physical key, for arbitrary input
klongs and arbitrary supplied deletion bits. -/
theorem KNode.lastVersionGivenDel_deadCount (n : KNode) (t : Time) (bits : List Nat) :
    (n.lastVersionGivenDel t bits).deadCount = 0 := by
  obtain ⟨pairs, hks, horder⟩ := n.lastVersionGivenDel_order t bits
  have hn : (pairs.map Prod.fst).Nodup :=
    List.pairwise_map.mpr (horder.imp (by intro a b h; omega))
  change (⟨(n.lastVersionGivenDel t bits).leaf, (n.lastVersionGivenDel t bits).ks⟩ : KNode).deadCount = 0
  rw [hks]
  exact KNode.newKlongs_deadCount _ t pairs hn

end SIS.Tree
