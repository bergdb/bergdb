import SIS.Tree.KlongShape
import SIS.Tree.SplitLiveFill

namespace SIS.Tree

open SIS SIS.Check

theorem klongsWf_keys_fold (full : List Klong) (pairs : List (Nat × NodeId))
    (start : Nat) (t : Time) (bits : List Nat) :
    ((pairs.map (fun q => Klong.key q.1 q.2)).zipIdx start).foldl
      (klongsWfStep full) (true,some t,bits) = (true,some t,bits) := by
  induction pairs generalizing start with
  | nil => rfl
  | cons q pairs ih =>
    rcases q with ⟨c,y⟩
    simpa only [List.map_cons,List.zipIdx_cons,List.foldl_cons,klongsWfStep,
      Option.isSome_some,Bool.and_self] using ih (start+1)

/-- Every one-time list of key klongs is well formed, including an empty
body and repeated compare values. -/
theorem klongsWf_newKlongs (t : Time) (pairs : List (Nat × NodeId)) :
    klongsWf (newKlongs t pairs) = true := by
  rw [klongsWf_eq_fold]
  simp only [newKlongs,List.zipIdx_cons,List.foldl_cons,klongsWfStep,Bool.and_self]
  rw [klongsWf_keys_fold]

theorem KNode.lastVersionGivenDel_wf (n : KNode) (t : Time) (del : List Nat) :
    klongsWf (n.lastVersionGivenDel t del).ks = true := by
  obtain ⟨pairs,he,_⟩ := n.lastVersionGivenDel_order t del
  rw [he]
  exact klongsWf_newKlongs t pairs

theorem halves_first_shape (leaf : Bool) (t : Time) (pairs ins : List (Nat × NodeId)) :
    ∃ out : List (Nat × NodeId),
      (halves leaf t ⟨leaf,newKlongs t pairs⟩ ins).1.ks = newKlongs t out := by
  cases hdrop : pairs.drop (pairs.length/2) with
  | nil =>
    cases ins <;> exact ⟨pairs.take (pairs.length/2),by
      simp [halves,newKlongs,KNode.size,← List.map_take,← List.map_drop,hdrop]⟩
  | cons b rest =>
    cases ins with
    | nil => exact ⟨pairs.take (pairs.length/2),by
        simp [halves,newKlongs,KNode.size,← List.map_take,← List.map_drop,hdrop]⟩
    | cons a ins =>
      by_cases hc : b.1 ≤ a.1
      · exact ⟨pairs.take (pairs.length/2),by
          simp [halves,newKlongs,KNode.size,← List.map_take,← List.map_drop,hdrop,hc]⟩
      · exact ⟨pairs.take (pairs.length/2) ++ a :: ins,by
          simp [halves,newKlongs,KNode.size,← List.map_take,← List.map_drop,hdrop,hc]⟩

theorem halves_newKlongs_wf (leaf : Bool) (t : Time) (pairs ins : List (Nat × NodeId)) :
    klongsWf (halves leaf t ⟨leaf,newKlongs t pairs⟩ ins).1.ks = true ∧
      klongsWf (halves leaf t ⟨leaf,newKlongs t pairs⟩ ins).2.1.ks = true := by
  obtain ⟨first,hfirst⟩ := halves_first_shape leaf t pairs ins
  obtain ⟨extra,hsecond⟩ := halves_second_shape leaf t pairs ins
  rw [hfirst,hsecond]
  exact ⟨klongsWf_newKlongs t first,klongsWf_newKlongs t _⟩

theorem halves_lastVersionGivenDel_wf (n : KNode) (t : Time) (del : List Nat)
    (ins : List (Nat × NodeId)) :
    klongsWf (halves n.leaf t (n.lastVersionGivenDel t del) ins).1.ks = true ∧
      klongsWf (halves n.leaf t (n.lastVersionGivenDel t del) ins).2.1.ks = true := by
  obtain ⟨pairs,he,_⟩ := n.lastVersionGivenDel_order t del
  have hleaf : (n.lastVersionGivenDel t del).leaf = n.leaf := rfl
  have hn : n.lastVersionGivenDel t del = ⟨n.leaf,newKlongs t pairs⟩ := by
    generalize n.lastVersionGivenDel t del = out at he hleaf ⊢
    cases out
    simp_all [newKlongs]
  rw [hn]
  exact halves_newKlongs_wf n.leaf t pairs ins

theorem replaceKlong_wf (ks : List Klong) (t c : Nat) (y : NodeId) (out : List Klong)
    (hw : klongsWf ks = true) (hr : replaceKlong ks t c y = .ok (some out)) :
    klongsWf out = true := by
  rwa [klongsWf_of_shape_eq out ks (replaceKlong_shape ks t c y out hr)]

end SIS.Tree
