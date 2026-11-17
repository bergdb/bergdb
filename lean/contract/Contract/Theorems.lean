/-
The contract package (bergdb 030-04, section 7.4 (b)): the theorems.

For any history that meets the writer's contract (`Meets`, Statement.lean):
at every time of the history, the tree meets the invariants, its contents are
the plain map's, and every get and every scan gives what the plain map gives.
"At every time" is the latest time and every earlier one.
-/
import Contract.Proof.Frame
import Contract.Proof.Get
import Contract.Proof.Scan

namespace Contract

theorem refMap_snoc (txs : List (List Op)) (ops : List Op) :
    refMap (txs ++ [ops]) = applyOps ops (refMap txs) := by
  simp [refMap, List.foldl_append]

/-- At every time t of a history that meets the contract, the tree at t meets
the invariants, and its contents are the plain map after the first t
transactions. -/
theorem Meets.at_time {p : Params} {txs : List (List Op)} {s : Tree} (h : Meets p txs s) :
    ∀ t ≤ txs.length,
      invOk p (s.at t) = true ∧ contents (s.at t) = refMap (txs.take t) := by
  induction h with
  | start s hs =>
    intro t ht
    obtain rfl : t = 0 := by simpa using ht
    exact ⟨hs.1, by simpa [refMap] using hs.2⟩
  | step txs s ops D s' hm hc ih =>
    intro t ht
    simp only [List.length_append, List.length_singleton] at ht
    by_cases hlt : t ≤ txs.length
    · obtain ⟨h1, h2⟩ := ih t hlt
      obtain ⟨h3, h4⟩ := hc.2.earlier (t := t) (Nat.lt_succ_of_le hlt) h1
      refine ⟨h3, ?_⟩
      rw [h4, h2, List.take_append_of_le_length hlt]
    · obtain rfl : t = txs.length + 1 := Nat.le_antisymm ht (Nat.lt_of_not_le hlt)
      have hco := hc.1
      simp only [contractOk, Bool.and_eq_true, beq_iff_eq, Nat.add_sub_cancel] at hco
      refine ⟨hco.1, ?_⟩
      have h5 := (ih txs.length (le_refl _)).2
      rw [List.take_length] at h5
      rw [hco.2, h5, List.take_of_length_le (by simp), refMap_snoc]

/-- TP7 for a history that meets the contract: at every time, the tree meets
the invariants. -/
theorem inv_right {p : Params} {txs : List (List Op)} {s : Tree} (h : Meets p txs s)
    (t : Time) (ht : t ≤ txs.length) : invOk p (s.at t) = true :=
  (h.at_time t ht).1

/-- TP10 for a history that meets the contract: a get at time t, the latest
or an earlier one, gives what the plain map after the first t transactions
gives. -/
theorem get_right {p : Params} {txs : List (List Op)} {s : Tree} (h : Meets p txs s)
    (t : Time) (ht : t ≤ txs.length) (k : Key) :
    get (s.at t) k = refGet (refMap (txs.take t)) k := by
  obtain ⟨h1, h2⟩ := h.at_time t ht
  rw [get_contents h1, h2]
  rfl

/-- TP11 for a history that meets the contract: a scan at time t, the latest
or an earlier one, forward or backward, with or without a start key and an
end key, gives what a scan of the plain map after the first t transactions
gives. -/
theorem scan_right {p : Params} {txs : List (List Op)} {s : Tree} (h : Meets p txs s)
    (t : Time) (ht : t ≤ txs.length) (req : ScanReq) (hreq : req.wf = true) (limit : Nat) :
    scan (s.at t) req limit = refScan (refMap (txs.take t)) req limit := by
  obtain ⟨h1, h2⟩ := h.at_time t ht
  rw [scan_contents h1 req hreq, h2]

end Contract
