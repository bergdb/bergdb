/-
bergdb 030-36: the entries of a planned child with puts and deletes.
A retained child gives the parent at most the klongs counted for it;
cut parts are new pointers and a kept or appended node keeps its base.
-/
import Contract.Proof.DnbDelTree

namespace Contract.PE

open DNB PeProof

variable {cf : Cfg} {i : Time} {s : Tree}

theorem child_entsD {b : Nat} {lvAll : List (Nat × NodeId)} {c : Nat} {y : NodeId} {w : VN}
    {g h : Nat} {acc acc' : Acc} {r : SR} (hl : lvAll.lookup c = some y)
    (hc : PlanSpecD b s g h y false w acc acc' r) :
    ((ents c w).filter (isAdded lvAll)).length ≤ r.up ∧
      (ents c w).length ≤ 1 + ((ents c w).filter (isAdded lvAll)).length ∧
      (((ents c w).filter (isAdded lvAll)).length = 0 → ents c w = [(c, some y)]) ∧
      (ents c w).head?.map (·.1) = some c := by
  obtain ⟨n, es, Fl, dec, _, rfl, hdec, _, _⟩ := hc.shape
  cases dec with
  | parts k =>
    obtain ⟨hov, hk⟩ := hdec k rfl
    have hpl := hc.parts (by omega)
    rw [hc.up]
    simp only [Bool.false_eq_true, false_and, ↓reduceIte, zero_add]
    rw [ite_eq_right (by omega)]
    simp only [ents]
    split
    · rename_i hk2
      have hall : (partEnts c Fl k false).filter (isAdded lvAll) = partEnts c Fl k false := by
        rw [List.filter_eq_self]
        intro e he
        simp [isAdded, partEnts_none c Fl k false e he]
      rw [hall, partEnts_length c Fl (by omega) false]
      refine ⟨hk, by omega, fun h0 => by omega, partEnts_head c Fl k false⟩
    · have h1 : ([(c, none)] : List (Nat × Option NodeId)).filter (isAdded lvAll) = [(c, none)] := by
        simp [List.filter, isAdded]
      rw [h1]
      simp only [List.length_singleton, List.head?_cons, Option.map_some]
      refine ⟨by omega, by omega, fun h0 => by omega, trivial⟩
  | same => simp [ents, isAdded_some hl]
  | append => simp [ents, isAdded_some hl]

end Contract.PE
