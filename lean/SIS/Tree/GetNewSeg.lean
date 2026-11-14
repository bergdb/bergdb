import SIS.Tree.GetSegRoot

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! A put of a key whose last segment has no tree yet (bergdb 024-12, TP10;
`OpGetOK`'s rules): the leaf of the segment before, with room, gets a klong to a
new segment leaf, which gets the put's klong (`setNode`'s creation). Every key
reads what it read but the put's key: a key through the new klong read nothing
before and reads nothing after, but the put's. -/

theorem getFromR_append_gen (N : NodeId → Option KNode) (V : NodeId → Option Nat) (t : Time)
    (fuel : Nat) (s : List Nat) (hs : s ≠ []) :
    ∀ (pre : List Nat) (r : NodeId), getFromR N V t fuel (pre ++ s) r =
      (segRootR N t fuel pre r).bind (fun rk => getFromR N V t fuel s rk) := by
  intro pre
  induction pre with
  | nil => intro r; rfl
  | cons c rest ih =>
    intro r
    have hne : rest ++ s ≠ [] := by simp [hs]
    obtain ⟨d, rest', he⟩ : ∃ d rest', rest ++ s = d :: rest' := by
      cases h : rest ++ s with
      | nil => exact absurd h hne
      | cons d rest' => exact ⟨d, rest', rfl⟩
    simp only [List.cons_append]
    rw [he]
    simp only [getFromR, segRootR]
    rw [← he]
    cases getEqR N t c fuel r with
    | none => rfl
    | some y =>
      simp only
      split
      · exact ih y
      · rfl

/-- The walk down a prefix is the same in two readers that agree at its visits
and on which reached nodes are key nodes. -/
theorem segRootR_frame_reach (N1 N2 : NodeId → Option KNode) (t : Time) (fuel : Nat)
    (r0 : NodeId) (hwf : ∀ x xn, ReachS N1 t r0 x → N1 x = some xn → klongsWf xn.ks = true)
    (hsome : ∀ y, ReachS N1 t r0 y → (N1 y).isSome = (N2 y).isSome) :
    ∀ (pre : List Nat) (r : NodeId), ReachS N1 t r0 r →
      (∀ q ∈ fromVisits N1 t fuel pre r, AgreeAt N1 N2 t q.1 q.2) →
      segRootR N1 t fuel pre r = segRootR N2 t fuel pre r := by
  intro pre
  induction pre with
  | nil => intro r _ _; rfl
  | cons c rest ih =>
    intro r hr h
    have hev : ∀ q ∈ eqVisits N1 t c fuel r, AgreeAt N1 N2 t q.1 q.2 := by
      intro q hq
      apply h q
      cases rest with
      | nil => exact hq
      | cons d rest' => simp only [fromVisits]; exact List.mem_append_left _ hq
    obtain ⟨he, _⟩ := getEqR_frame N1 N2 t c fuel r hev
    simp only [segRootR]
    rw [← he]
    cases hg : getEqR N1 t c fuel r with
    | none => rfl
    | some y =>
      simp only
      have hy : ReachS N1 t r0 y := getEqR_reach N1 t r0 c hwf fuel r y hr hg
      rw [← hsome y hy]
      split
      · apply ih y hy
        intro q hq
        apply h q
        cases rest with
        | nil => simp [fromVisits] at hq
        | cons d rest' =>
          simp only [fromVisits, hg]
          exact List.mem_append_right _ hq
      · rfl

theorem deadOver_empty_add (p : Params) (t : Time) (cl : Nat) (v : NodeId) :
    deadOver p ((⟨true, []⟩ : KNode).add t (.key cl v)) = false := by
  simp [deadOver, KNode.deadCount, KNode.add, KNode.lastBitmap, KNode.lastTime, lastBitmapOf]

end SIS.Tree
