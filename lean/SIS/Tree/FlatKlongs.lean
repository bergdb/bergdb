import SIS.Tree.KlongPreservation

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- A last version has one time klong and only key klongs after it. This
shape does not require ordered or distinct compare values. -/
def FlatKlongs (ks : List Klong) : Prop :=
  ∃ t pairs, ks = newKlongs t pairs

theorem flatKlongs_wf (ks : List Klong) (h : FlatKlongs ks) :
    klongsWf ks = true := by
  obtain ⟨t, pairs, rfl⟩ := h
  exact klongsWf_newKlongs t pairs

theorem KNode.lastVersionGivenDel_flat (n : KNode) (t : Time) (bits : List Nat) :
    FlatKlongs (n.lastVersionGivenDel t bits).ks := by
  obtain ⟨pairs, hp, _⟩ := n.lastVersionGivenDel_order t bits
  exact ⟨t, pairs, hp⟩

theorem KNode.lastVersion_flat (n : KNode) (t : Time) :
    FlatKlongs (n.lastVersion t).ks := n.lastVersionGivenDel_flat t _

theorem key_body_of_shape (ks : List Klong) (pairs : List (Nat × NodeId))
    (h : ks.map klongShape = pairs.map (fun q => Klong.key q.1 0)) :
    ∃ out : List (Nat × NodeId), ks = out.map (fun q => Klong.key q.1 q.2) := by
  induction pairs generalizing ks with
  | nil => exact ⟨[], by simpa using h⟩
  | cons q pairs ih =>
    cases ks with
    | nil => simp at h
    | cons k ks =>
      have hh := List.cons.inj h
      obtain ⟨out, hout⟩ := ih ks hh.2
      cases k with
      | time t => simp [klongShape] at hh
      | del bits => simp [klongShape] at hh
      | key cv y => exact ⟨(cv, y) :: out, by simp [hout]⟩

theorem flatKlongs_of_shape (ks old : List Klong)
    (he : ks.map klongShape = old.map klongShape) (h : FlatKlongs old) :
    FlatKlongs ks := by
  obtain ⟨t, pairs, rfl⟩ := h
  cases ks with
  | nil => simp [newKlongs] at he
  | cons k ks =>
    simp only [newKlongs, List.map_cons, klongShape, List.map_map] at he
    have hh := List.cons.inj he
    have hbody : ks.map klongShape = pairs.map (fun q => Klong.key q.1 0) := hh.2
    obtain ⟨out, hout⟩ := key_body_of_shape ks pairs hbody
    cases k with
    | key cv y => simp at hh
    | del bits => simp at hh
    | time u =>
      have hut : u = t := by simpa [klongShape] using hh.1
      subst u
      exact ⟨t, out, by simp [newKlongs, hout]⟩

theorem flatKlongs_replaceKlong (ks out : List Klong) (t cv : Nat) (y : NodeId)
    (h : FlatKlongs ks) (hr : replaceKlong ks t cv y = .ok (some out)) :
    FlatKlongs out := flatKlongs_of_shape _ _ (replaceKlong_shape _ _ _ _ _ hr) h

theorem insertSorted_key_body (pairs : List (Nat × NodeId)) (cv : Nat) (y : NodeId) :
    ∃ out : List (Nat × NodeId),
      insertSorted (pairs.map (fun q => Klong.key q.1 q.2)) cv y =
        out.map (fun q => Klong.key q.1 q.2) := by
  induction pairs with
  | nil => exact ⟨[(cv, y)], rfl⟩
  | cons q pairs ih =>
    obtain ⟨out, hout⟩ := ih
    by_cases hc : cv < q.1
    · exact ⟨(cv, y) :: q :: pairs, by simp [insertSorted, hc]⟩
    · exact ⟨q :: out, by simp [insertSorted, hc, hout]⟩

theorem flatKlongs_insertSorted (ks : List Klong) (cv : Nat) (y : NodeId)
    (h : FlatKlongs ks) : FlatKlongs (insertSorted ks cv y) := by
  obtain ⟨t, pairs, rfl⟩ := h
  obtain ⟨out, hout⟩ := insertSorted_key_body pairs cv y
  exact ⟨t, out, by simp only [newKlongs, insertSorted, hout]⟩

theorem flatKlongs_rename_first (t cv : Nat) (y : NodeId) (rest : List Klong)
    (h : FlatKlongs (.time t :: .key cv y :: rest)) (newCv : Nat) :
    FlatKlongs (.time t :: .key newCv y :: rest) := by
  obtain ⟨u, pairs, hp⟩ := h
  cases pairs with
  | nil => simp [newKlongs] at hp
  | cons q pairs =>
    have hh : rest = pairs.map (fun q => Klong.key q.1 q.2) := by
      simpa only [newKlongs, List.map_cons, List.cons.injEq] using
        (List.cons.inj (List.cons.inj hp).2).2
    exact ⟨t, (newCv, y) :: pairs, by simp [newKlongs, hh]⟩

theorem halves_flat_wf (leaf : Bool) (t : Time) (last : KNode)
    (ins : List (Nat × NodeId)) (h : FlatKlongs last.ks) :
    klongsWf (halves leaf t last ins).1.ks = true ∧
      klongsWf (halves leaf t last ins).2.1.ks = true := by
  obtain ⟨u, pairs, hp⟩ := h
  have he : halves leaf t last ins = halves leaf t ⟨leaf, newKlongs t pairs⟩ ins := by
    simp [halves, KNode.size, hp, newKlongs]
  rw [he]
  exact halves_newKlongs_wf leaf t pairs ins

theorem flatKlongs_rename_after_head (old : List Klong) (k : Klong) (cv : Nat)
    (y : NodeId) (rest : List Klong) (newCv : Nat)
    (he : old = k :: .key cv y :: rest) (hf : FlatKlongs old) :
    FlatKlongs (k :: .key newCv y :: rest) := by
  obtain ⟨t, pairs, hp⟩ := hf
  cases pairs with
  | nil => simp [newKlongs, he] at hp
  | cons q pairs =>
    rw [he] at hp
    have hk : k = .time t := (List.cons.inj hp).1
    have hr : rest = pairs.map (fun p => Klong.key p.1 p.2) :=
      (List.cons.inj (List.cons.inj hp).2).2
    exact ⟨t, (newCv, y) :: pairs, by simp [newKlongs, hk, hr]⟩

end SIS.Tree
