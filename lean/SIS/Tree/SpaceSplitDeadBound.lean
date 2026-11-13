import SIS.Tree.SplitMergeDead

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- The number of physical pairs shadowed by a later equal compare value. -/
def shadowCount : List (Nat × NodeId) → Nat
  | [] => 0
  | q :: qs => (if qs.any (fun r => r.1 == q.1) then 1 else 0) + shadowCount qs

theorem shadowCount_eq_filter (pairs : List (Nat × NodeId)) :
    shadowCount pairs = (pairs.zipIdx.filter (fun q =>
      (pairs.drop (q.2 + 1)).any (fun r => r.1 == q.1.1))).length := by
  induction pairs with
  | nil => rfl
  | cons q pairs ih =>
    simp only [List.zipIdx_cons, List.filter_cons, List.drop_succ_cons, List.drop_zero]
    rw [List.zipIdx_succ]
    simp only [List.filter_map, Function.comp_def]
    cases h : pairs.any (fun r => r.1 == q.1) <;>
      simp [shadowCount, h, ← ih, Nat.add_comm]

/-- On a one-time key body the physical dead counter counts precisely
shadowed pairs. This does not require the pairs to be ordered or distinct. -/
theorem KNode.newKlongs_deadCount_eq (leaf : Bool) (t : Time)
    (pairs : List (Nat × NodeId)) :
    (⟨leaf, newKlongs t pairs⟩ : KNode).deadCount = shadowCount pairs := by
  unfold KNode.deadCount KNode.lastBitmap
  rw [lastBitmapOf_newKlongs]
  simp only [newKlongs, List.zipIdx_cons, List.filter_cons, List.contains_nil,
    Bool.false_or, Bool.false_eq_true, ↓reduceIte]
  rw [List.zipIdx_map, List.zipIdx_succ]
  simp only [List.filter_map, List.map_map, List.length_map, Function.comp_def,
    Prod.map, id_eq, List.drop_succ_cons, ← List.map_drop, List.any_map]
  exact (shadowCount_eq_filter pairs).symm

/-- Appending one physical pointer creates at most one newly dead key,
even when its compare value already has many older versions. -/
theorem shadowCount_append_one (pairs : List (Nat × NodeId)) (q : Nat × NodeId) :
    shadowCount (pairs ++ [q]) = shadowCount pairs +
      (if pairs.any (fun r => r.1 == q.1) then 1 else 0) := by
  induction pairs with
  | nil => simp [shadowCount]
  | cons a pairs ih =>
    rcases a with ⟨a,y⟩
    rcases q with ⟨b,z⟩
    dsimp only at ih
    by_cases he : a = b
    · subst b
      simp only [List.cons_append, shadowCount, List.any_append, List.any_cons,
        List.any_nil, beq_self_eq_true, Bool.or_false, Bool.true_or, Bool.or_true,
        ↓reduceIte]
      rw [ih]
      cases hc : pairs.any (fun r => r.1 == a) <;> simp <;> omega
    · have he' : b ≠ a := Ne.symm he
      simp only [List.cons_append, shadowCount, List.any_append, List.any_cons,
        List.any_nil, Bool.or_false, beq_eq_false_iff_ne.mpr he,
        beq_eq_false_iff_ne.mpr he', Bool.false_or, Bool.or_false]
      rw [ih]
      omega

theorem shadowCount_append_le (pairs ins : List (Nat × NodeId)) :
    shadowCount (pairs ++ ins) ≤ shadowCount pairs + ins.length := by
  induction ins generalizing pairs with
  | nil => simp
  | cons q ins ih =>
    have hh := ih (pairs ++ [q])
    have he := shadowCount_append_one pairs q
    simp only [List.append_assoc, List.singleton_append, List.length_cons] at hh ⊢
    split at he <;> omega

theorem shadowCount_zero_of_distinct (pairs : List (Nat × NodeId))
    (hn : (pairs.map Prod.fst).Nodup) : shadowCount pairs = 0 := by
  have hh := KNode.newKlongs_deadCount true 0 pairs hn
  rwa [KNode.newKlongs_deadCount_eq] at hh

/-- Arbitrary upward inserts in a normalized body create no more dead
physical keys than the number of inserted klongs. -/
theorem KNode.newKlongs_append_deadCount_le (leaf : Bool) (t : Time)
    (pairs ins : List (Nat × NodeId)) (hn : (pairs.map Prod.fst).Nodup) :
    (⟨leaf, newKlongs t (pairs ++ ins)⟩ : KNode).deadCount ≤ ins.length := by
  rw [KNode.newKlongs_deadCount_eq]
  have hh := shadowCount_append_le pairs ins
  rwa [shadowCount_zero_of_distinct pairs hn, Nat.zero_add] at hh

/-- A space split, including arbitrary upward inserts, leaves at most
one dead key per inserted pointer in each output. No common-side or
uniqueness premise is imposed on the insert list. -/
theorem halves_deadCount_le_inserts (leaf : Bool) (t : Time)
    (pairs ins : List (Nat × NodeId)) (hs : CvSorted pairs) :
    (halves leaf t ⟨leaf, newKlongs t pairs⟩ ins).1.deadCount ≤ ins.length ∧
      (halves leaf t ⟨leaf, newKlongs t pairs⟩ ins).2.1.deadCount ≤ ins.length := by
  have hf : ((pairs.take (pairs.length / 2)).map Prod.fst).Nodup :=
    List.pairwise_map.mpr ((hs.sublist (List.take_sublist _ _)).imp
      (by intro a b hab; omega))
  have hsecond : ((secondSplitPairs leaf pairs).map Prod.fst).Nodup :=
    List.pairwise_map.mpr ((secondSplitPairs_order leaf pairs hs).imp
      (by intro a b hab; omega))
  cases hd : pairs.drop (pairs.length / 2) with
  | nil =>
    have hp : pairs = [] := by
      apply List.length_eq_zero_iff.mp
      have hh := List.drop_eq_nil_iff.mp hd
      omega
    subst pairs
    have he : halves leaf t ⟨leaf, newKlongs t []⟩ ins =
        (⟨leaf, newKlongs t []⟩, ⟨leaf, newKlongs t ins⟩, 0) := by
      cases leaf <;> cases ins <;> simp [halves, newKlongs, KNode.size, key_zero_ite]
    rw [he]
    exact ⟨by rw [KNode.newKlongs_deadCount _ _ _ (by simp)]; omega,
      KNode.newKlongs_append_deadCount_le leaf t [] ins (by simp)⟩
  | cons r rest =>
    have hr : (pairs.drop (pairs.length / 2)).head? = some r := by simp [hd]
    rw [halves_shape leaf t pairs ins r hr]
    have hfirst0 : (⟨leaf, newKlongs t (pairs.take (pairs.length / 2))⟩ : KNode).deadCount ≤
        ins.length := by rw [KNode.newKlongs_deadCount _ _ _ hf]; omega
    have hsecond0 : (⟨leaf, newKlongs t (secondSplitPairs leaf pairs)⟩ : KNode).deadCount ≤
        ins.length := by rw [KNode.newKlongs_deadCount _ _ _ hsecond]; omega
    have hfirstIns := KNode.newKlongs_append_deadCount_le leaf t _ ins hf
    have hsecondIns : (⟨leaf, newKlongs t (secondSplitPairs leaf pairs ++
        ins.map (fun q => (splitLocalCv leaf r.1 q.1, q.2)))⟩ : KNode).deadCount ≤ ins.length := by
      have hb := KNode.newKlongs_append_deadCount_le leaf t _
        (ins.map (fun q => (splitLocalCv leaf r.1 q.1, q.2))) hsecond
      simpa only [List.length_map] using hb
    split
    · split
      · exact ⟨hfirst0, hsecondIns⟩
      · exact ⟨hfirstIns, hsecond0⟩
    · exact ⟨hfirstIns, hsecond0⟩

/-- The actual normalized split input discharges the order premise.
In particular, two upward klongs give the bound two in each half. -/
theorem halves_normalized_deadCount_le (n : KNode) (t : Time) (bits : List Nat)
    (ins : List (Nat × NodeId)) :
    (halves n.leaf t (n.lastVersionGivenDel t bits) ins).1.deadCount ≤ ins.length ∧
      (halves n.leaf t (n.lastVersionGivenDel t bits) ins).2.1.deadCount ≤ ins.length := by
  obtain ⟨pairs, hks, hs⟩ := n.lastVersionGivenDel_order t bits
  have he : n.lastVersionGivenDel t bits = ⟨n.leaf, newKlongs t pairs⟩ := by
    have hl : (n.lastVersionGivenDel t bits).leaf = n.leaf := rfl
    cases ho : n.lastVersionGivenDel t bits
    simp_all [newKlongs]
  rw [he]
  exact halves_deadCount_le_inserts n.leaf t pairs ins hs

end SIS.Tree
