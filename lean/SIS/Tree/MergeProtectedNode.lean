import SIS.Tree.MergeFrozenPrefix

namespace SIS.Tree

open SIS SIS.Check

private def onlyKeyStep (del : List Nat) (acc : Option (Option (Nat × Nat)))
    (q : Klong × Nat) : Option (Option (Nat × Nat)) :=
  match acc with
  | none => none
  | some cur => match q.1 with
    | .key c _ =>
      if del.contains q.2 then acc else match cur with
        | some (_,cv) => if c != cv then none else some (some (q.2,c))
        | none => some (some (q.2,c))
    | _ => acc

private def onlyKeyAllows (c : Nat) : Option (Option (Nat × Nat)) → Prop
  | none => False
  | some none => True
  | some (some (_,a)) => a = c

private theorem onlyKeyStep_back (del : List Nat) (acc : Option (Option (Nat × Nat)))
    (q : Klong × Nat) (c : Nat) (ha : onlyKeyAllows c (onlyKeyStep del acc q)) :
    onlyKeyAllows c acc ∧ ∀ a y i, q = (.key a y,i) → i ∉ del → a = c := by
  rcases q with ⟨k,i⟩
  cases acc with
  | none => exact ha.elim
  | some cur =>
    cases k with
    | time t => exact ⟨ha,by intro a y j he; cases he⟩
    | del bits => exact ⟨ha,by intro a y j he; cases he⟩
    | key a y =>
      by_cases hi : i ∈ del
      · have hh : onlyKeyAllows c (some cur) := by simpa [onlyKeyStep,hi] using ha
        refine ⟨hh,?_⟩
        intro b z j he hj
        cases he
        exact (hj hi).elim
      · cases cur with
        | none =>
          have hac : a = c := by simpa [onlyKeyStep,onlyKeyAllows,hi] using ha
          exact ⟨trivial,by intro b z j he _; cases he; exact hac⟩
        | some jc =>
          rcases jc with ⟨j,b⟩
          have hab : a = b := by
            by_cases he : a = b
            · exact he
            · simp [onlyKeyStep,onlyKeyAllows,hi,he] at ha
          have hac : a = c := by simpa [onlyKeyStep,onlyKeyAllows,hi,hab] using ha
          exact ⟨by simpa [onlyKeyAllows,← hab] using hac,
            by intro d z e he _; cases he; exact hac⟩

private theorem onlyKeyFold_back (del : List Nat) (ks : List (Klong × Nat))
    (acc : Option (Option (Nat × Nat))) (c : Nat)
    (ha : onlyKeyAllows c (ks.foldl (onlyKeyStep del) acc)) :
    onlyKeyAllows c acc ∧
      ∀ a y i, (.key a y,i) ∈ ks → i ∉ del → a = c := by
  induction ks generalizing acc with
  | nil => exact ⟨ha,by simp⟩
  | cons q ks ih =>
    obtain ⟨hstep,htail⟩ := ih _ ha
    obtain ⟨hacc,hhead⟩ := onlyKeyStep_back del acc q c hstep
    refine ⟨hacc,?_⟩
    intro a y i hm hi
    simp only [List.mem_cons] at hm
    rcases hm with he | hm
    · exact hhead a y i he.symm hi
    · exact htail a y i hm hi

/-- A successful only-live-klong test permits at most one live compare
value, even when a physical node contains shadowed versions. -/
theorem KNode.onlyLiveKlong_some_cnt_le_one (n : KNode) (i : Nat)
    (hi : n.onlyLiveKlong = some i) : n.cnt ≤ 1 := by
  unfold KNode.onlyLiveKlong at hi
  change (match n.ks.zipIdx.foldl (onlyKeyStep n.lastBitmap) (some none) with
    | some (some (j,_)) => some j | _ => none) = some i at hi
  cases hr : n.ks.zipIdx.foldl (onlyKeyStep n.lastBitmap) (some none) with
  | none => simp only [hr] at hi; cases hi
  | some cur =>
    cases cur with
    | none => simp only [hr] at hi; cases hi
    | some jc =>
      rcases jc with ⟨j,c⟩
      have hall := (onlyKeyFold_back n.lastBitmap n.ks.zipIdx (some none) c
        (by rw [hr]; exact rfl)).2
      have hsub : ∀ a ∈ n.live.map Prod.fst, a ∈ [c] := by
        intro a ha
        obtain ⟨y,k,hm,hk⟩ := (n.live_has_key a).mp ha
        exact List.mem_singleton.mpr (hall a y k hm hk)
      have hlen := n.live_keys_nodup.length_le_of_subset hsub
      simpa only [List.length_map,List.length_singleton,KNode.cnt] using hlen

theorem KNode.onlyLiveKlong_none_of_cnt_ge_two (n : KNode) (hn : 2 ≤ n.cnt) :
    n.onlyLiveKlong = none := by
  cases hi : n.onlyLiveKlong with
  | none => rfl
  | some i => have := n.onlyLiveKlong_some_cnt_le_one i hi; omega

/-- The retained prefix of a split prevents the first half from passing
the root-collapse test. This concerns its actual live count. -/
theorem halves_first_protected_not_unary (p : Params) (hp : MergeParamsOK p)
    (leaf : Bool) (t : Time) (pairs ins : List (Nat × NodeId))
    (hs : pairs.Pairwise (fun a b => a.1 < b.1))
    (hfull : p.splitAbove < (⟨leaf,newKlongs t pairs⟩ : KNode).size) :
    (halves leaf t ⟨leaf,newKlongs t pairs⟩ ins).1.onlyLiveKlong = none := by
  apply KNode.onlyLiveKlong_none_of_cnt_ge_two
  exact Nat.le_trans hp.1 (halves_first_protected_fill p hp leaf t pairs ins hs hfull)

/-- The same barrier survives a merge into one node or into two: the first
output keeps enough distinct compare values from its left input. -/
theorem mergeKlongs_first_protected_not_unary (p : Params) (hp : MergeParamsOK p)
    (inner : Bool) (t : Time) (cR : Nat) (left right : List (Nat × NodeId))
    (hn : (left.map Prod.fst).Nodup) (hleft : p.mergeBelow ≤ left.length) :
    (⟨!inner,newKlongs t (mergeKlongs inner p.mergeMax cR left right).1⟩ : KNode).onlyLiveKlong = none := by
  apply KNode.onlyLiveKlong_none_of_cnt_ge_two
  exact Nat.le_trans hp.1
    (mergeKlongs_first_protected_fill p hp inner t cR left right hn hleft)

end SIS.Tree
