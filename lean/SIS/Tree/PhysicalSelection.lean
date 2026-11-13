import SIS.Tree.KlongPreservation

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- The physical evidence needed when a writer turns a selected key into
a bitmap bit. No well-formedness or ordering premise is built into it. -/
def LivePhysicalKey (ks : List Klong) (del : List Nat) (i cv : Nat) (y : NodeId) : Prop :=
  ks[i]? = some (.key cv y) ∧ i ∉ del

def PhysicalChoiceOK (ks : List Klong) (del : List Nat)
    (choice : Option (Nat × Nat × NodeId)) : Prop :=
  ∀ i cv y, choice = some (i, cv, y) → LivePhysicalKey ks del i cv y

/-- The next-child selector used by LE-b. -/
def nextPhysicalStep (del : List Nat) (best : Option (Nat × Nat × NodeId))
    (q : Klong × Nat) : Option (Nat × Nat × NodeId) :=
  match q.1 with
  | .key cv y =>
    if del.contains q.2 then best else
      match best with
      | none => some (q.2, cv, y)
      | some (_, jcv, _) => if cv ≤ jcv then some (q.2, cv, y) else best
  | _ => best

theorem nextPhysicalStep_ok (ks : List Klong) (del : List Nat)
    (best : Option (Nat × Nat × NodeId)) (q : Klong × Nat)
    (hb : PhysicalChoiceOK ks del best) (hq : q ∈ ks.zipIdx) :
    PhysicalChoiceOK ks del (nextPhysicalStep del best q) := by
  rcases q with ⟨k, i⟩
  have hi := List.mem_zipIdx_iff_getElem?.mp hq
  cases k with
  | time t => exact hb
  | del bits => exact hb
  | key cv y =>
    by_cases hd : i ∈ del
    · simpa [nextPhysicalStep, hd] using hb
    · have hnew : PhysicalChoiceOK ks del (some (i, cv, y)) := by
        intro a b z he
        cases he
        exact ⟨hi, hd⟩
      unfold nextPhysicalStep
      simp only [show del.contains i = false by simpa using hd, Bool.false_eq_true, ↓reduceIte]
      cases best with
      | none => exact hnew
      | some old =>
        rcases old with ⟨j, a, z⟩
        dsimp only
        split <;> assumption

theorem nextPhysicalFold_ok (ks : List Klong) (del : List Nat)
    (xs : List (Klong × Nat)) (hx : ∀ q ∈ xs, q ∈ ks.zipIdx)
    (best : Option (Nat × Nat × NodeId)) (hb : PhysicalChoiceOK ks del best) :
    PhysicalChoiceOK ks del (xs.foldl (nextPhysicalStep del) best) := by
  induction xs generalizing best with
  | nil => exact hb
  | cons q xs ih =>
    exact ih (fun a ha => hx a (List.mem_cons_of_mem q ha)) _
      (nextPhysicalStep_ok ks del best q hb (hx q List.mem_cons_self))

theorem nextPhysical_live (ks : List Klong) (del : List Nat) (i cv : Nat) (y : NodeId)
    (h : ks.zipIdx.foldl (nextPhysicalStep del) none = some (i, cv, y)) :
    LivePhysicalKey ks del i cv y :=
  nextPhysicalFold_ok ks del ks.zipIdx (by intro q hq; exact hq) none
    (by intro a b z he; cases he) i cv y h

theorem KNode.delete_bitmap_changes_of_physical (n : KNode) (cv i : Nat) (y : NodeId)
    (h : LivePhysicalKey n.ks n.lastBitmap i cv y) :
    bitsUnion n.lastBitmap (n.bitsOf cv) ≠ n.lastBitmap := by
  intro he
  have hi : i ∈ n.bitsOf cv :=
    (n.mem_bitsOf_iff cv i).mpr ⟨y, List.mem_zipIdx_iff_getElem?.mpr h.1⟩
  have hm := (mem_bitsUnion_iff n.lastBitmap (n.bitsOf cv) i).mpr (Or.inr hi)
  rw [he] at hm
  exact h.2 hm

theorem KNode.delete_bitmap_changes_of_live (n : KNode) (cv : Nat)
    (h : cv ∈ n.live.map Prod.fst) :
    bitsUnion n.lastBitmap (n.bitsOf cv) ≠ n.lastBitmap := by
  obtain ⟨y, i, hi, hdel⟩ := (n.live_has_key cv).mp h
  exact n.delete_bitmap_changes_of_physical cv i y
    ⟨List.mem_zipIdx_iff_getElem?.mp hi, hdel⟩

/-- Every index kept by the merge's selector is an undeleted physical key;
the side selectors also retain its actual compare value. -/
def MergeIndicesOK (ks : List Klong) (del : List Nat)
    (acc : Option Nat × Option (Nat × Nat) × Option (Nat × Nat)) : Prop :=
  (∀ i, acc.1 = some i → ∃ cv y, LivePhysicalKey ks del i cv y) ∧
  (∀ i cv, acc.2.1 = some (i, cv) → ∃ y, LivePhysicalKey ks del i cv y) ∧
  (∀ i cv, acc.2.2 = some (i, cv) → ∃ y, LivePhysicalKey ks del i cv y)

def mergePhysicalStep (del : List Nat) (cx : Nat)
    (acc : Option Nat × Option (Nat × Nat) × Option (Nat × Nat))
    (q : Klong × Nat) : Option Nat × Option (Nat × Nat) × Option (Nat × Nat) :=
  match q.1 with
  | .key cv _ =>
    if del.contains q.2 then acc
    else if cv == cx then (some q.2, acc.2.1, acc.2.2)
    else if cx < cv then
      (acc.1, (match acc.2.1 with
        | none => some (q.2, cv)
        | some (_, cva) => if cv ≤ cva then some (q.2, cv) else acc.2.1), acc.2.2)
    else
      (acc.1, acc.2.1, (match acc.2.2 with
        | none => some (q.2, cv)
        | some (_, cvb) => if cvb ≤ cv then some (q.2, cv) else acc.2.2))
  | _ => acc

theorem mergePhysicalStep_ok (ks : List Klong) (del : List Nat) (cx : Nat)
    (acc : Option Nat × Option (Nat × Nat) × Option (Nat × Nat)) (q : Klong × Nat)
    (ha : MergeIndicesOK ks del acc) (hq : q ∈ ks.zipIdx) :
    MergeIndicesOK ks del (mergePhysicalStep del cx acc q) := by
  rcases q with ⟨k, i⟩
  have hi := List.mem_zipIdx_iff_getElem?.mp hq
  cases k with
  | time t => exact ha
  | del bits => exact ha
  | key cv y =>
    by_cases hd : i ∈ del
    · simpa [mergePhysicalStep, hd] using ha
    · have hnew : LivePhysicalKey ks del i cv y := ⟨hi, hd⟩
      have hone : ∀ j, some i = some j → ∃ a z, LivePhysicalKey ks del j a z := by
        intro j he; cases he; exact ⟨cv, y, hnew⟩
      have hpair : ∀ j a, some (i, cv) = some (j, a) →
          ∃ z, LivePhysicalKey ks del j a z := by
        intro j a he; cases he; exact ⟨y, hnew⟩
      unfold mergePhysicalStep
      simp only [show del.contains i = false by simpa using hd, Bool.false_eq_true, ↓reduceIte]
      split
      · exact ⟨hone, ha.2⟩
      · split
        · refine ⟨ha.1, ?_, ha.2.2⟩
          cases hp : acc.2.1 with
          | none => exact hpair
          | some p =>
            rcases p with ⟨j, a⟩
            dsimp only
            split
            · exact hpair
            · simpa only [hp] using ha.2.1
        · refine ⟨ha.1, ha.2.1, ?_⟩
          cases hp : acc.2.2 with
          | none => exact hpair
          | some p =>
            rcases p with ⟨j, a⟩
            dsimp only
            split
            · exact hpair
            · simpa only [hp] using ha.2.2

theorem mergePhysicalFold_ok (ks : List Klong) (del : List Nat) (cx : Nat)
    (xs : List (Klong × Nat)) (hx : ∀ q ∈ xs, q ∈ ks.zipIdx)
    (acc : Option Nat × Option (Nat × Nat) × Option (Nat × Nat))
    (ha : MergeIndicesOK ks del acc) :
    MergeIndicesOK ks del (xs.foldl (mergePhysicalStep del cx) acc) := by
  induction xs generalizing acc with
  | nil => exact ha
  | cons q xs ih =>
    exact ih (fun a ha => hx a (List.mem_cons_of_mem q ha)) _
      (mergePhysicalStep_ok ks del cx acc q ha (hx q List.mem_cons_self))

theorem mergeIdx_live (n : KNode) (cx : Nat) :
    MergeIndicesOK n.ks n.lastBitmap (mergeIdx n cx) := by
  refine mergePhysicalFold_ok n.ks n.lastBitmap cx n.ks.zipIdx
    (by intro q hq; exact hq) (none, none, none) ?_
  refine ⟨?_, ?_, ?_⟩
  · intro i h; cases h
  · intro i cv h; cases h
  · intro i cv h; cases h

theorem KNode.live_of_physical_cv (n : KNode) (i cv : Nat)
    (hi : ∃ a y, LivePhysicalKey n.ks n.lastBitmap i a y)
    (hc : n.cv? i = some cv) : cv ∈ n.live.map Prod.fst := by
  obtain ⟨a, y, hk, hd⟩ := hi
  have ha : a = cv := by simpa only [KNode.cv?, hk, Option.some.injEq] using hc
  subst a
  apply (n.live_has_key cv).mpr
  exact ⟨y, i, List.mem_zipIdx_iff_getElem?.mpr hk, hd⟩

theorem KNode.mergeIdx_cv_live (n : KNode) (cx i cv : Nat)
    (hi : (mergeIdx n cx).1 = some i ∨
      (∃ a, (mergeIdx n cx).2.1 = some (i, a)) ∨
      (∃ a, (mergeIdx n cx).2.2 = some (i, a)))
    (hc : n.cv? i = some cv) : cv ∈ n.live.map Prod.fst := by
  apply n.live_of_physical_cv i cv ?_ hc
  rcases hi with hi | ⟨a, ha⟩ | ⟨a, ha⟩
  · exact (mergeIdx_live n cx).1 i hi
  · obtain ⟨y, hy⟩ := (mergeIdx_live n cx).2.1 i a ha
    exact ⟨a, y, hy⟩
  · obtain ⟨y, hy⟩ := (mergeIdx_live n cx).2.2 i a ha
    exact ⟨a, y, hy⟩

theorem KNode.mergeIdx_current_cv_live (n : KNode) (cx i cv : Nat)
    (hi : (mergeIdx n cx).1 = some i) (hc : n.cv? i = some cv) :
    cv ∈ n.live.map Prod.fst := n.mergeIdx_cv_live cx i cv (Or.inl hi) hc

theorem KNode.mergeIdx_above_cv_live (n : KNode) (cx i a cv : Nat)
    (hi : (mergeIdx n cx).2.1 = some (i, a)) (hc : n.cv? i = some cv) :
    cv ∈ n.live.map Prod.fst := n.mergeIdx_cv_live cx i cv (Or.inr (Or.inl ⟨a, hi⟩)) hc

theorem KNode.mergeIdx_below_cv_live (n : KNode) (cx i a cv : Nat)
    (hi : (mergeIdx n cx).2.2 = some (i, a)) (hc : n.cv? i = some cv) :
    cv ∈ n.live.map Prod.fst := n.mergeIdx_cv_live cx i cv (Or.inr (Or.inr ⟨a, hi⟩)) hc

end SIS.Tree
