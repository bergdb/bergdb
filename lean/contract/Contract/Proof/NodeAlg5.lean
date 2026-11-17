/-
The contract package (bergdb 030-10): the node algebra of the delete of a full
node. The writer replaces the node by its last version under the delete's
bitmap (`KNode.lastVersionGivenDel` with `delUnion`): a time klong and the
live klongs without the compare value. And `dropCv` (order, length,
members), the number of live klongs against the node's size, and the first
klong of a node after a bitmap is added or set.
-/
import Contract.Proof.NodeAlg4

namespace Contract

/-! ## 1. A last version under a bitmap -/

/-- The last version under the bitmap `del`: its key klongs are a list of
distinct compare values with the members of the live klongs under `del`,
sorted. -/
theorem lastVersionGivenDel_struct (n : MNode) (t : Time) (del : List Nat) :
    ∃ m : List (Nat × NodeId), (n.lastVersionGivenDel t del).ks =
      .time t :: (m.mergeSort (fun a b => decide (a.1 ≤ b.1))).map (fun p => .key p.1 p.2) ∧
      m.Pairwise (fun a b => a.1 ≠ b.1) ∧ ∀ p, p ∈ m ↔ p ∈ liveWith del (ksOf n).zipIdx := by
  refine ⟨_, rfl, ?_⟩
  unfold liveWith ksOf
  rw [List.zipIdx_map, List.foldl_map]
  refine foldl_sim_post _ _
    (fun (b c : List (Nat × NodeId)) =>
      b.Pairwise (fun a b => a.1 ≠ b.1) ∧ c.Pairwise CvLt ∧ ∀ p, p ∈ b ↔ p ∈ c)
    (fun b c => b.Pairwise (fun a b => a.1 ≠ b.1) ∧ ∀ p, p ∈ b ↔ p ∈ c)
    ?_ (fun _ _ h => ⟨h.1, h.2.2⟩) _ _ _ ⟨List.Pairwise.nil, List.Pairwise.nil, fun _ => Iff.rfl⟩
  rintro b c ⟨k, i⟩ ⟨hb, hc, hmem⟩
  cases k with
  | time x => exact ⟨hb, hc, hmem⟩
  | del bs => exact ⟨hb, hc, hmem⟩
  | key c' y =>
    by_cases hd : i ∈ del
    · simp only [kOf, Prod.map, id, List.contains_iff_mem, hd, ite_true]
      exact ⟨hb, hc, hmem⟩
    · simp only [kOf, Prod.map, id, List.contains_iff_mem, hd, ite_false]
      obtain ⟨h1, h2⟩ := setCv_spec hb c' y
      refine ⟨h1, insertCv_sorted c' y hc, fun p => ?_⟩
      rw [h2, mem_insertCv_iff hc, hmem]

/-- The last version under the bitmap `del`: a time klong and the live klongs
under `del`, in their order. -/
theorem lastVersionGivenDel_ks (n : MNode) (t : Time) (del : List Nat) :
    ksOf (n.lastVersionGivenDel t del) =
      Klong.time t :: (liveWith del (ksOf n).zipIdx).map (fun cy => Klong.key cy.1 cy.2) := by
  obtain ⟨m, hks, hd, hmem⟩ := lastVersionGivenDel_struct n t del
  rw [show ksOf (n.lastVersionGivenDel t del) = (n.lastVersionGivenDel t del).ks.map kOf from rfl,
    hks]
  have h1 := List.pairwise_mergeSort (le := fun a b : Nat × NodeId => decide (a.1 ≤ b.1))
    (fun a b c hab hbc => by simp only [decide_eq_true_eq] at hab hbc ⊢; omega)
    (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) m
  have h2 : (m.mergeSort (fun a b => decide (a.1 ≤ b.1))).Pairwise (fun a b => a.1 ≠ b.1) :=
    ((List.mergeSort_perm m _).pairwise_iff (fun h => Ne.symm h)).mpr hd
  have h3 : (m.mergeSort (fun a b => decide (a.1 ≤ b.1))).Pairwise CvLt :=
    (h1.and h2).imp (fun h => lt_of_le_of_ne (by simpa using h.1) h.2)
  rw [cvSorted_ext h3 (liveWith_sorted _ _) (fun p => by rw [List.mem_mergeSort, hmem])]
  simp [kOf]

/-- The delete's last version (`handleFull` of a delete): a time klong and the
live klongs without compare value cv. -/
theorem lastVersionGivenDel_union (n : MNode) (t : Time) (cv : Nat) :
    ksOf (n.lastVersionGivenDel t (delUnion n cv)) =
      Klong.time t :: (dropCv cv (live (ksOf n))).map (fun cy => Klong.key cy.1 cy.2) := by
  rw [lastVersionGivenDel_ks,
    liveWith_union cv _ _ _ (union_cond n cv (L := ksOf n) (fun _ _ h => h))]
  rfl

theorem lastVersionGivenDel_leaf (n : MNode) (t : Time) (del : List Nat) :
    (n.lastVersionGivenDel t del).leaf = n.leaf := rfl

/-! ## 2. `dropCv` -/

theorem dropCv_sorted (cv : Nat) {l : List (Nat × NodeId)} (hs : l.Pairwise CvLt) :
    (dropCv cv l).Pairwise CvLt :=
  hs.filter _

theorem dropCv_length_le (cv : Nat) (l : List (Nat × NodeId)) :
    (dropCv cv l).length ≤ l.length :=
  List.length_filter_le _ _

theorem mem_dropCv {cv : Nat} {l : List (Nat × NodeId)} {p : Nat × NodeId} :
    p ∈ dropCv cv l ↔ p ∈ l ∧ p.1 ≠ cv := by
  simp [dropCv]

/-! ## 3. The live klongs against the size -/

theorem live_length_size {n : MNode} {t0 : Time} {rest : List MKlong}
    (h : n.ks = .time t0 :: rest) : (live (ksOf n)).length + 1 ≤ n.size := by
  rw [← ksOf_length]
  exact live_length_le ⟨t0, rest.map kOf, by simp [ksOf, h, kOf]⟩

theorem dropCv_length_size {n : MNode} {t0 : Time} {rest : List MKlong}
    (h : n.ks = .time t0 :: rest) (cv : Nat) :
    (dropCv cv (live (ksOf n))).length + 1 ≤ n.size :=
  le_trans (Nat.add_le_add_right (dropCv_length_le cv _) 1) (live_length_size h)

/-! ## 4. The first klong after a bitmap -/

theorem add_head {n : MNode} {t0 : Time} {rest : List MKlong} (h : n.ks = .time t0 :: rest)
    (t : Time) (k : MKlong) : (n.add t k).ks.head? = n.ks.head? := by
  obtain ⟨rest', h'⟩ := add_first (t := t) k h
  rw [h', h]
  rfl

theorem setDel_head {n : MNode} {t t0 : Time} {rest : List MKlong} (ht : hasTransDel n t = true)
    (h : n.ks = .time t0 :: rest) (b : List Nat) :
    (n.setAt (n.size - 1) (.del b)).ks.head? = n.ks.head? := by
  obtain ⟨rest', h'⟩ := setDel_first ht h b
  rw [h', h]
  rfl

end Contract
