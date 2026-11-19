/-
bergdb 026-24 (copied for 030-21), phase 3: the lemma of settle (026-23, section 1.2, the proof's
part 1 for one parent). PE settles a parent's children on lists only: an
empty child is dropped, a small child is joined with a neighbour, a long list
is cut into pieces (rebalance, and emit's cut into parts), and the parent's
first entry gets the empty key. This file proves, on lists, that these steps
keep:

* the keys: the child level read as one list (`flat`: each child's list, an
  inner child's first entry given its compare value in the parent) is the
  same before and after each step (`Step.flat_eq`), so the contents, which
  the contract reads off the tree in this order (`Contract.listAt`), are
  kept;
* the order: each child lies in its range, from max(lo, its compare value)
  to the next child's compare value or the parent's bound, in strictly
  increasing order (`RangedFrom`, the contract's RangeOK for the parent and
  its children; `Step.ranged`), and renaming the parent's first compare value
  to the empty key keeps it (`ranged_renameFirst`, LE-b).

And that the cut of emit (`cutList` with `partSizes`, lean/pe/Pe/Plan.lean)
makes nonempty pieces whose concatenation is the list (`cutList_flatten`,
`cutList_ne_nil`), each of at most ceil(n / k) entries (`cutList_length_le`).

Nothing here is a tree, a node or a time: lists only.
-/
import Mathlib.Tactic
import Contract.Statement
import Contract.PeWriter

namespace PeProof

open Contract Contract.PE

variable {α : Type}

/-! ## Definitions -/

/-- A parent's entries: for each child, its compare value in the parent and the
child's own list. -/
abbrev Ents (α : Type) := List (Nat × List (Nat × α))

/-- A child's list as the parent sees it: an inner child's first entry (the
empty key) gets the child's compare value in the parent. -/
def eff (inner : Bool) (e : Nat × List (Nat × α)) : List (Nat × α) :=
  if inner then renameHead e.1 e.2 else e.2

/-- The child level as one list. -/
def flat (inner : Bool) (es : Ents α) : List (Nat × α) := es.flatMap (eff inner)

/-- The pieces of a cut as the parent's entries: the first keeps the compare
value c; each other one its first compare value, and an inner piece starts
with the empty key. -/
def cutEnts (inner : Bool) (c : Nat) : List (List (Nat × α)) → Ents α
  | [] => []
  | P :: Ps => (c, P) :: Ps.map (fun Q => (headCv Q, if inner then renameHead 0 Q else Q))

/-- One step of settle at a parent (026-23, 1.2): drop an empty child; join a
child with the next one; cut a child's list into nonempty pieces. -/
inductive Step (inner : Bool) : Ents α → Ents α → Prop
  | drop (pre post : Ents α) (c : Nat) : Step inner (pre ++ (c, []) :: post) (pre ++ post)
  | join (pre post : Ents α) (cL cR : Nat) (L R : List (Nat × α)) (hL : L ≠ []) :
      Step inner (pre ++ (cL, L) :: (cR, R) :: post)
        (pre ++ (cL, L ++ eff inner (cR, R)) :: post)
  | cut (pre post : Ents α) (c : Nat) (Ps : List (List (Nat × α))) (hne : ∀ P ∈ Ps, P ≠ [])
      (hPs : Ps ≠ []) :
      Step inner (pre ++ (c, Ps.flatten) :: post) (pre ++ cutEnts inner c Ps ++ post)

/-! ## The keys -/

theorem renameHead_append (c : Nat) {L : List (Nat × α)} (hL : L ≠ []) (X : List (Nat × α)) :
    renameHead c (L ++ X) = renameHead c L ++ X := by
  cases L with
  | nil => exact absurd rfl hL
  | cons a r => obtain ⟨_, _⟩ := a; rfl

theorem eff_append (inner : Bool) (c : Nat) {L : List (Nat × α)} (hL : L ≠ []) (X : List (Nat × α)) :
    eff inner (c, L ++ X) = eff inner (c, L) ++ X := by
  unfold eff
  split
  · exact renameHead_append c hL X
  · rfl

theorem renameHead_renameHead (c d : Nat) (L : List (Nat × α)) :
    renameHead c (renameHead d L) = renameHead c L := by
  cases L with
  | nil => rfl
  | cons a r => obtain ⟨_, _⟩ := a; rfl

theorem renameHead_headCv (L : List (Nat × α)) : renameHead (headCv L) L = L := by
  cases L with
  | nil => rfl
  | cons a r => obtain ⟨_, _⟩ := a; rfl

theorem eff_piece (inner : Bool) (Q : List (Nat × α)) :
    eff inner (headCv Q, if inner then renameHead 0 Q else Q) = Q := by
  unfold eff
  cases inner
  · rfl
  · simp only [ite_true]
    rw [renameHead_renameHead]
    exact renameHead_headCv Q

theorem flat_cutEnts (inner : Bool) (c : Nat) :
    ∀ (Ps : List (List (Nat × α))), (∀ P ∈ Ps, P ≠ []) →
      flat inner (cutEnts inner c Ps) = eff inner (c, Ps.flatten)
  | [], _ => by simp [flat, cutEnts, eff, renameHead]
  | P :: Qs, h => by
    have hP : P ≠ [] := h P List.mem_cons_self
    simp only [cutEnts, flat, List.flatMap_cons, List.flatten_cons]
    rw [eff_append inner c hP]
    congr 1
    rw [List.flatMap_map]
    simp only [eff_piece]
    simp

/-- **The lemma of settle, the keys**: a step keeps the child level. -/
theorem Step.flat_eq {inner : Bool} {es es' : Ents α} (h : Step inner es es') :
    flat inner es' = flat inner es := by
  cases h with
  | drop pre post c =>
    simp [flat, eff, renameHead]
  | join pre post cL cR L R hL =>
    simp only [flat, List.flatMap_append, List.flatMap_cons]
    rw [eff_append inner cL hL]
    simp
  | cut pre post c Ps hne _ =>
    simp only [flat, List.flatMap_append, List.flatMap_cons]
    have := flat_cutEnts inner c Ps hne
    simp only [flat] at this
    rw [this, List.append_assoc]

theorem Steps.flat_eq {inner : Bool} {es es' : Ents α}
    (h : Relation.ReflTransGen (Step inner) es es') : flat inner es' = flat inner es := by
  induction h with
  | refl => rfl
  | tail _ hs ih => rw [hs.flat_eq, ih]

/-! ## The order: each child in its range -/

/-- The order of a list's entries: by compare value, strictly. -/
abbrev CvLtA (a b : Nat × α) : Prop := a.1 < b.1

/-- c is below the bound nx (none: no bound). -/
def Below (c : Nat) : Option Nat → Prop
  | none => True
  | some h => c < h

/-- The bound nx is at or below the bound nx'. -/
def BoundLe : Option Nat → Option Nat → Prop
  | _, none => True
  | none, some _ => False
  | some a, some b => a ≤ b

/-- The bound after a child: the next child's compare value, or hi. -/
def nextCv (rest : Ents α) (hi : Option Nat) : Option Nat :=
  match rest with
  | (c, _) :: _ => some c
  | [] => hi

/-- A child (c, L) with the bound nx after it (the contract's RangeOK for the
child's klong in the parent and for the child's live klongs): c is below nx;
the child's list as the parent sees it is in strictly increasing order and
below nx, and in a segment leaf at or above max lo c. -/
def ChildOk (inner : Bool) (lo : Nat) (nx : Option Nat) (e : Nat × List (Nat × α)) : Prop :=
  Below e.1 nx ∧ (eff inner e).Pairwise CvLtA ∧
    ∀ x ∈ eff inner e, Below x.1 nx ∧ (inner = true ∨ max lo e.1 ≤ x.1)

/-- Every child of a parent with the range [lo, hi) in its range. -/
def RangedFrom (inner : Bool) (lo : Nat) (hi : Option Nat) : Ents α → Prop
  | [] => True
  | e :: rest => ChildOk inner lo (nextCv rest hi) e ∧ RangedFrom inner lo hi rest

theorem below_mono {c : Nat} {nx nx' : Option Nat} (h : Below c nx) (hle : BoundLe nx nx') :
    Below c nx' := by
  cases nx with
  | none => cases nx' with
    | none => trivial
    | some b => exact absurd hle (by simp [BoundLe])
  | some a => cases nx' with
    | none => trivial
    | some b => simp only [Below, BoundLe] at h hle ⊢; omega

theorem below_trans {a b : Nat} {nx : Option Nat} (hab : a < b) (h : Below b nx) : Below a nx := by
  cases nx with
  | none => trivial
  | some c => simp only [Below] at h ⊢; omega

theorem childOk_mono {inner : Bool} {lo : Nat} {nx nx' : Option Nat} {e : Nat × List (Nat × α)}
    (h : ChildOk inner lo nx e) (hle : BoundLe nx nx') : ChildOk inner lo nx' e :=
  ⟨below_mono h.1 hle, h.2.1, fun x hx => ⟨below_mono (h.2.2 x hx).1 hle, (h.2.2 x hx).2⟩⟩

theorem nextCv_append (pre rest : Ents α) (hi : Option Nat) :
    nextCv (pre ++ rest) hi = nextCv pre (nextCv rest hi) := by
  cases pre with
  | nil => rfl
  | cons a r => rfl

theorem ranged_append (inner : Bool) (lo : Nat) (hi : Option Nat) (rest : Ents α) :
    ∀ pre : Ents α, RangedFrom inner lo hi (pre ++ rest) ↔
      RangedFrom inner lo (nextCv rest hi) pre ∧ RangedFrom inner lo hi rest
  | [] => by simp [RangedFrom]
  | e :: pre => by
    simp only [List.cons_append, RangedFrom]
    rw [ranged_append inner lo hi rest pre, nextCv_append]
    tauto

theorem ranged_mono {inner : Bool} {lo : Nat} {hi hi' : Option Nat} (hle : BoundLe hi hi') :
    ∀ es : Ents α, RangedFrom inner lo hi es → RangedFrom inner lo hi' es
  | [], _ => trivial
  | [_], h => ⟨childOk_mono h.1 hle, trivial⟩
  | _ :: e' :: rest, h => ⟨h.1, ranged_mono hle (e' :: rest) h.2⟩

theorem boundLe_of_below {c : Nat} {nx : Option Nat} (h : Below c nx) : BoundLe (some c) nx := by
  cases nx with
  | none => trivial
  | some b => simp only [Below, BoundLe] at h ⊢; omega

/-- **Settle, drop**: an empty child dropped. -/
theorem ranged_drop {inner : Bool} {lo : Nat} {hi : Option Nat} (pre post : Ents α) (c : Nat)
    (h : RangedFrom inner lo hi (pre ++ (c, []) :: post)) : RangedFrom inner lo hi (pre ++ post) := by
  rw [ranged_append] at h ⊢
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨ranged_mono (boundLe_of_below h2.1) pre h1, h3⟩

theorem head_le_of_sorted {L : List (Nat × α)} (hs : L.Pairwise CvLtA) {a : Nat × α}
    (ha : L.head? = some a) : ∀ x ∈ L, a.1 ≤ x.1 := by
  cases L with
  | nil => simp at ha
  | cons b r =>
    simp only [List.head?_cons, Option.some.injEq] at ha
    subst ha
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact le_refl _
    · exact le_of_lt ((List.pairwise_cons.mp hs).1 x hx)

theorem renameHead_head? (c : Nat) {R : List (Nat × α)} (hR : R ≠ []) :
    ∃ y, (renameHead c R).head? = some (c, y) := by
  cases R with
  | nil => exact absurd rfl hR
  | cons a r => exact ⟨a.2, rfl⟩

/-- The entries of a child's list as the parent sees it are at or above its
compare value. -/
theorem childOk_lower {inner : Bool} {lo : Nat} {nx : Option Nat} {c : Nat} {R : List (Nat × α)}
    (h : ChildOk inner lo nx (c, R)) : ∀ x ∈ eff inner (c, R), c ≤ x.1 := by
  intro x hx
  rcases (h.2.2 x hx).2 with hi | hl
  · subst hi
    have hR : R ≠ [] := by
      rintro rfl
      simp [eff, renameHead] at hx
    obtain ⟨y, hy⟩ := renameHead_head? c hR
    exact head_le_of_sorted (α := α) h.2.1 (by simpa [eff] using hy) x hx
  · simp only at hl
    omega

/-- **Settle, join**: a child joined with the next one. -/
theorem ranged_join {inner : Bool} {lo : Nat} {hi : Option Nat} (pre post : Ents α) (cL cR : Nat)
    (L R : List (Nat × α)) (hL : L ≠ [])
    (h : RangedFrom inner lo hi (pre ++ (cL, L) :: (cR, R) :: post)) :
    RangedFrom inner lo hi (pre ++ (cL, L ++ eff inner (cR, R)) :: post) := by
  rw [ranged_append] at h ⊢
  obtain ⟨h1, ⟨hL1, hR1, h3⟩⟩ := h
  refine ⟨h1, ⟨?_, h3⟩⟩
  simp only [nextCv] at hL1 hR1 ⊢
  have hcl : cL < cR := hL1.1
  have hlow := childOk_lower hR1
  refine ⟨below_trans hcl hR1.1, ?_, ?_⟩
  · rw [eff_append inner cL hL, List.pairwise_append]
    refine ⟨hL1.2.1, hR1.2.1, fun a ha b hb => ?_⟩
    have := (hL1.2.2 a ha).1
    have := hlow b hb
    simp only [Below] at *
    show a.1 < b.1
    omega
  · rw [eff_append inner cL hL]
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · refine ⟨below_trans ?_ hR1.1, (hL1.2.2 x hx).2⟩
      have := (hL1.2.2 x hx).1
      simpa [Below] using this
    · refine ⟨(hR1.2.2 x hx).1, ?_⟩
      rcases (hR1.2.2 x hx).2 with hi | hl
      · exact Or.inl hi
      · right; simp only at hl ⊢; omega

/-- Pieces of a sorted list, as a parent's entries (each its first compare
value, an inner piece with the empty key first): each in its range. -/
theorem ranged_pieces {inner : Bool} {lo : Nat} {nx : Option Nat} :
    ∀ (Qs : List (List (Nat × α))), (∀ Q ∈ Qs, Q ≠ []) → Qs.flatten.Pairwise CvLtA →
      (∀ x ∈ Qs.flatten, Below x.1 nx ∧ (inner = true ∨ lo ≤ x.1)) →
      RangedFrom inner lo nx (Qs.map (fun Q => (headCv Q, if inner then renameHead 0 Q else Q)))
  | [], _, _, _ => trivial
  | Q :: Qs, hne, hs, hb => by
    have hQ : Q ≠ [] := hne Q List.mem_cons_self
    rw [List.flatten_cons, List.pairwise_append] at hs
    refine ⟨?_, ranged_pieces Qs (fun Q' h => hne Q' (List.mem_cons_of_mem _ h)) hs.2.1
      (fun x hx => hb x (by rw [List.flatten_cons]; exact List.mem_append_right _ hx))⟩
    obtain ⟨a, r, rfl⟩ := List.exists_cons_of_ne_nil hQ
    have hhead : headCv (a :: r) = a.1 := rfl
    have hlow : ∀ x ∈ a :: r, a.1 ≤ x.1 := head_le_of_sorted hs.1 rfl
    -- the bound after this piece: the next piece's first compare value, or nx
    have hnext : ∀ x ∈ a :: r, Below x.1 (nextCv (Qs.map (fun Q => (headCv Q,
        if inner then renameHead 0 Q else Q))) nx) := by
      intro x hx
      cases Qs with
      | nil =>
        exact (hb x (by simp only [List.flatten_cons, List.flatten_nil, List.append_nil]; exact hx)).1
      | cons Q2 Qs2 =>
        have hQ2 : Q2 ≠ [] := hne Q2 (by simp)
        obtain ⟨b, r2, rfl⟩ := List.exists_cons_of_ne_nil hQ2
        simp only [List.map_cons, nextCv, Below]
        exact hs.2.2 x hx b (by simp)
    refine ⟨?_, ?_, ?_⟩
    · show Below (headCv (a :: r)) _
      rw [hhead]; exact hnext a List.mem_cons_self
    · show (eff inner (headCv (a :: r), if inner then renameHead 0 (a :: r) else (a :: r))).Pairwise _
      rw [eff_piece]; exact hs.1
    · show ∀ x ∈ eff inner (headCv (a :: r), if inner then renameHead 0 (a :: r) else (a :: r)), _
      rw [eff_piece]
      intro x hx
      refine ⟨hnext x hx, ?_⟩
      rcases (hb x (by rw [List.flatten_cons]; exact List.mem_append_left _ hx)).2 with hi | hl
      · exact Or.inl hi
      · right; show max lo (headCv (a :: r)) ≤ x.1
        rw [hhead]; have := hlow x hx; omega

/-- **Settle, cut**: a child's list cut into nonempty pieces. -/
theorem ranged_cut {inner : Bool} {lo : Nat} {hi : Option Nat} (pre post : Ents α) (c : Nat)
    (Ps : List (List (Nat × α))) (hne : ∀ P ∈ Ps, P ≠ []) (hPs : Ps ≠ [])
    (h : RangedFrom inner lo hi (pre ++ (c, Ps.flatten) :: post)) :
    RangedFrom inner lo hi (pre ++ cutEnts inner c Ps ++ post) := by
  obtain ⟨P1, Qs, rfl⟩ := List.exists_cons_of_ne_nil hPs
  have hP1 : P1 ≠ [] := hne P1 List.mem_cons_self
  rw [ranged_append] at h
  rw [List.append_assoc, ranged_append]
  obtain ⟨h1, hc, hpost⟩ := h
  simp only [cutEnts, List.cons_append]
  refine ⟨h1, ?_⟩
  simp only [RangedFrom]
  rw [ranged_append]
  simp only [nextCv] at hc
  have hlow := childOk_lower hc
  obtain ⟨hcb, hcs, hcx⟩ := hc
  rw [List.flatten_cons, eff_append inner c hP1] at hcs hcx hlow
  rw [List.pairwise_append] at hcs
  refine ⟨⟨?_, hcs.1, fun x hx => ⟨?_, (hcx x (List.mem_append_left _ hx)).2⟩⟩,
    ranged_pieces Qs (fun Q h => hne Q (List.mem_cons_of_mem _ h)) hcs.2.1 ?_, hpost⟩
  · -- c is below the next piece's first compare value, or the bound after
    cases Qs with
    | nil => simpa [nextCv] using hcb
    | cons Q2 Qs2 =>
      have hQ2 : Q2 ≠ [] := hne Q2 (by simp)
      obtain ⟨b, r2, rfl⟩ := List.exists_cons_of_ne_nil hQ2
      have hne1 : eff inner (c, P1) ≠ [] := by
        obtain ⟨a, r, rfl⟩ := List.exists_cons_of_ne_nil hP1
        unfold eff; split <;> simp [renameHead]
      obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil _ hne1
      have h1 := hlow a (List.mem_append_left _ ha)
      have h2 := hcs.2.2 a ha b (by simp)
      simp only [List.map_cons, nextCv, Below, headCv, List.head?_cons, Option.map_some,
        Option.getD_some] at h2 ⊢
      show c < b.1
      exact lt_of_le_of_lt h1 h2
  · cases Qs with
    | nil => simpa [nextCv] using (hcx x (List.mem_append_left _ hx)).1
    | cons Q2 Qs2 =>
      have hQ2 : Q2 ≠ [] := hne Q2 (by simp)
      obtain ⟨b, r2, rfl⟩ := List.exists_cons_of_ne_nil hQ2
      simp only [List.map_cons, nextCv, Below, headCv, List.head?_cons, Option.map_some,
        Option.getD_some]
      exact hcs.2.2 x hx b (by simp)
  · intro x hx
    refine ⟨(hcx x (List.mem_append_right _ hx)).1, ?_⟩
    rcases (hcx x (List.mem_append_right _ hx)).2 with hi | hl
    · exact Or.inl hi
    · right; simp only at hl; omega

/-- **Settle, the empty key** (LE-b): the parent's first compare value set to
0 keeps every child in its range. -/
theorem ranged_renameFirst {inner : Bool} {lo : Nat} {hi : Option Nat} (c : Nat)
    (L : List (Nat × α)) (rest : Ents α) (h : RangedFrom inner lo hi ((c, L) :: rest)) :
    RangedFrom inner lo hi ((0, L) :: rest) := by
  obtain ⟨⟨hb, hs, hx⟩, hr⟩ := h
  refine ⟨⟨?_, ?_, ?_⟩, hr⟩
  · rcases Nat.eq_zero_or_pos c with rfl | hc
    · exact hb
    · exact below_trans hc hb
  · cases inner
    · simpa [eff] using hs
    · cases L with
      | nil => simp [eff, renameHead]
      | cons a r =>
        simp only [eff, ite_true, renameHead, List.pairwise_cons] at hs ⊢
        refine ⟨fun b hb' => ?_, hs.2⟩
        have := hs.1 b hb'
        simp only [CvLtA] at this ⊢
        omega
  · have hb0 : Below 0 (nextCv rest hi) := by
      rcases Nat.eq_zero_or_pos c with rfl | hc
      · exact hb
      · exact below_trans hc hb
    intro x hx'
    cases inner
    · simp only [eff, Bool.false_eq_true, ite_false] at hx' hx
      refine ⟨(hx x hx').1, Or.inr ?_⟩
      rcases (hx x hx').2 with h0 | h0
      · exact absurd h0 (by simp)
      · simp only at h0 ⊢; omega
    · refine ⟨?_, Or.inl rfl⟩
      cases L with
      | nil => simp [eff, renameHead] at hx'
      | cons a r =>
        simp only [eff, ite_true, renameHead, List.mem_cons] at hx' hx
        rcases hx' with rfl | hr
        · exact hb0
        · exact (hx x (Or.inr hr)).1

/-- **The lemma of settle, the order**: a step keeps every child in its range. -/
theorem Step.ranged {inner : Bool} {lo : Nat} {hi : Option Nat} {es es' : Ents α}
    (h : Step inner es es') (hr : RangedFrom inner lo hi es) : RangedFrom inner lo hi es' := by
  cases h with
  | drop pre post c => exact ranged_drop pre post c hr
  | join pre post cL cR L R hL => exact ranged_join pre post cL cR L R hL hr
  | cut pre post c Ps hne hPs => exact ranged_cut pre post c Ps hne hPs hr

theorem Steps.ranged {inner : Bool} {lo : Nat} {hi : Option Nat} {es es' : Ents α}
    (h : Relation.ReflTransGen (Step inner) es es') (hr : RangedFrom inner lo hi es) :
    RangedFrom inner lo hi es' := by
  induction h with
  | refl => exact hr
  | tail _ hs ih => exact hs.ranged ih

/-- Every entry of the child level is at or above the first child's compare
value. -/
theorem ranged_lower {inner : Bool} {lo : Nat} {hi : Option Nat} :
    ∀ (e : Nat × List (Nat × α)) (rest : Ents α), RangedFrom inner lo hi (e :: rest) →
      ∀ x ∈ flat inner (e :: rest), e.1 ≤ x.1
  | e, [], h, x, hx => by
    simp only [flat, List.flatMap_cons, List.flatMap_nil, List.append_nil] at hx
    exact childOk_lower (c := e.1) (R := e.2) h.1 x hx
  | e, e2 :: rest2, h, x, hx => by
    rw [flat, List.flatMap_cons, List.mem_append] at hx
    rcases hx with hx | hx
    · exact childOk_lower (c := e.1) (R := e.2) h.1 x hx
    · have h12 : e.1 < e2.1 := h.1.1
      have := ranged_lower e2 rest2 h.2 x hx
      omega

/-- The child level read in order is in strictly increasing order of its
compare values when every child is in its range. -/
theorem flat_sorted {inner : Bool} {lo : Nat} {hi : Option Nat} :
    ∀ es : Ents α, RangedFrom inner lo hi es → (flat inner es).Pairwise CvLtA
  | [], _ => by simp [flat]
  | e :: rest, ⟨he, hr⟩ => by
    rw [flat, List.flatMap_cons, List.pairwise_append]
    refine ⟨he.2.1, flat_sorted rest hr, fun a ha b hb => ?_⟩
    cases rest with
    | nil => simp at hb
    | cons e2 rest2 =>
      have ha' := (he.2.2 a ha).1
      simp only [nextCv, Below] at ha'
      have := ranged_lower e2 rest2 hr b hb
      show a.1 < b.1
      omega

/-! ## The cut of emit -/

theorem cutList_flatten {β : Type} : ∀ (l : List β) (sizes : List Nat), sizes.sum = l.length →
    (cutList l sizes).flatten = l
  | l, [], h => by
    simp only [List.sum_nil] at h
    rw [List.eq_nil_of_length_eq_zero h.symm]
    rfl
  | l, s :: r, h => by
    simp only [cutList, List.flatten_cons]
    rw [cutList_flatten (l.drop s) r (by simp only [List.sum_cons] at h; simp only [List.length_drop]; omega),
      List.take_append_drop]

theorem cutList_ne_nil {β : Type} : ∀ (l : List β) (sizes : List Nat), sizes.sum = l.length →
    (∀ s ∈ sizes, 0 < s) → ∀ P ∈ cutList l sizes, P ≠ []
  | _, [], _, _ => by simp [cutList]
  | l, s :: r, h, hp => by
    intro P hP
    simp only [cutList, List.mem_cons] at hP
    rcases hP with rfl | hP
    · have hs := hp s List.mem_cons_self
      simp only [List.sum_cons] at h
      intro he
      have := congrArg List.length he
      rw [List.length_take, List.length_nil] at this
      omega
    · exact cutList_ne_nil (l.drop s) r
        (by simp only [List.sum_cons] at h; simp only [List.length_drop]; omega)
        (fun s' h' => hp s' (List.mem_cons_of_mem _ h')) P hP

theorem cutList_length_le {β : Type} : ∀ (l : List β) (sizes : List Nat) (m : Nat),
    (∀ s ∈ sizes, s ≤ m) → ∀ P ∈ cutList l sizes, P.length ≤ m
  | _, [], _, _ => by simp [cutList]
  | l, s :: r, m, hm => by
    intro P hP
    simp only [cutList, List.mem_cons] at hP
    rcases hP with rfl | hP
    · have := hm s List.mem_cons_self
      simp only [List.length_take]
      omega
    · exact cutList_length_le (l.drop s) r m (fun s' h' => hm s' (List.mem_cons_of_mem _ h')) P hP

theorem cutList_length {β : Type} (l : List β) (sizes : List Nat) :
    (cutList l sizes).length = sizes.length := by
  induction sizes generalizing l with
  | nil => rfl
  | cons s r ih => simp [cutList, ih]

theorem partSizes_length (n k : Nat) (cf : Bool) : (partSizes n k cf).length = k := by
  simp [partSizes]

theorem partSizes_bounds {n k : Nat} {cf : Bool} :
    ∀ s ∈ partSizes n k cf, n / k ≤ s ∧ s ≤ n / k + 1 := by
  intro s hs
  simp only [partSizes, List.mem_map, List.mem_range] at hs
  obtain ⟨j, _, rfl⟩ := hs
  split <;> split <;> omega

theorem sum_ceilFirst (b e : Nat) : ∀ k : Nat,
    ((List.range k).map (fun j => if j < e then b + 1 else b)).sum = k * b + min k e
  | 0 => by simp
  | k + 1 => by
    rw [List.sum_range_succ, sum_ceilFirst b e k]
    split <;> simp [Nat.succ_mul, Nat.min_def] <;> (try split) <;> omega

theorem sum_floorFirst (b K e : Nat) : ∀ k : Nat,
    ((List.range k).map (fun j => if K - e ≤ j then b + 1 else b)).sum = k * b + (k - (K - e))
  | 0 => by simp
  | k + 1 => by
    rw [List.sum_range_succ, sum_floorFirst b K e k]
    split <;> simp [Nat.succ_mul] <;> omega

/-- The parts' sizes add up to n. -/
theorem partSizes_sum {n k : Nat} (hk : 0 < k) (cf : Bool) : (partSizes n k cf).sum = n := by
  have he : n % k < k := Nat.mod_lt n hk
  have hn : k * (n / k) + n % k = n := Nat.div_add_mod n k
  cases cf
  · simp only [partSizes, Bool.false_eq_true, ite_false]
    rw [sum_floorFirst]
    have : k - (k - n % k) = n % k := by omega
    rw [this]
    exact hn
  · simp only [partSizes, ite_true]
    rw [sum_ceilFirst, Nat.min_eq_right (le_of_lt he)]
    exact hn

/-- **The cut of emit**: k parts of a list of n entries, 0 < k ≤ n, are
nonempty, make the list again, and hold at most ceil(n / k) entries each. -/
theorem cut_spec {β : Type} (l : List β) {k : Nat} (hk : 0 < k) (hkn : k ≤ l.length) (cf : Bool) :
    (cutList l (partSizes l.length k cf)).flatten = l ∧
    (∀ P ∈ cutList l (partSizes l.length k cf), P ≠ []) ∧
    (∀ P ∈ cutList l (partSizes l.length k cf), P.length ≤ l.length / k + 1) ∧
    (cutList l (partSizes l.length k cf)).length = k := by
  refine ⟨cutList_flatten l _ (partSizes_sum hk cf), cutList_ne_nil l _ (partSizes_sum hk cf) ?_,
    cutList_length_le l _ _ (fun s hs => (partSizes_bounds s hs).2), ?_⟩
  · intro s hs
    have := (partSizes_bounds s hs).1
    have : 1 ≤ l.length / k := (Nat.one_le_div_iff hk).mpr hkn
    omega
  · rw [cutList_length, partSizes_length]

end PeProof
