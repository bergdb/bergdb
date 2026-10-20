/-
Proofs, part 1: histories, the structure P, reachability.
-/
import SIS.Assumptions

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type}

/-! ### Histories -/

@[simp] theorem upTo_nil (t : Time) : History.upTo ([] : History V) t = [] := rfl

theorem upTo_append (h₁ h₂ : History V) (t : Time) :
    (h₁ ++ h₂).upTo t = h₁.upTo t ++ h₂.upTo t := by
  simp [History.upTo, List.filter_append]

theorem mem_upTo {h : History V} {t : Time} {e : Entry V} :
    e ∈ h.upTo t ↔ e ∈ h ∧ e.time ≤ t := by
  simp [History.upTo]

theorem upTo_upTo (h : History V) {t t' : Time} (ht : t ≤ t') :
    (h.upTo t').upTo t = h.upTo t := by
  simp only [History.upTo, List.filter_filter]
  apply List.filter_congr
  intro e _
  by_cases h1 : e.time ≤ t
  · have : e.time ≤ t' := Nat.le_trans h1 ht
    simp [h1, this]
  · simp [h1]

theorem upTo_upTo' (h : History V) {t t' : Time} (ht : t' ≤ t) :
    (h.upTo t').upTo t = h.upTo t' := by
  simp only [History.upTo, List.filter_filter]
  apply List.filter_congr
  intro e _
  by_cases h1 : e.time ≤ t'
  · have : e.time ≤ t := Nat.le_trans h1 ht
    simp [h1, this]
  · simp [h1]

theorem upTo_of_forall (h : History V) (t : Time) (hh : ∀ e ∈ h, e.time ≤ t) :
    h.upTo t = h := by
  simp only [History.upTo]
  rw [List.filter_eq_self]
  intro e he
  simpa using hh e he

theorem upTo_eq_nil (h : History V) (t : Time) (hh : ∀ e ∈ h, t < e.time) :
    h.upTo t = [] := by
  simp only [History.upTo]
  rw [List.filter_eq_nil_iff]
  intro e he
  have := hh e he
  simp
  omega

/-- Two histories with the same entries up to time t' agree up to every
earlier time. -/
theorem upTo_eq_of_le {h₁ h₂ : History V} {t t' : Time} (ht : t ≤ t')
    (heq : h₁.upTo t' = h₂.upTo t') : h₁.upTo t = h₂.upTo t := by
  rw [← upTo_upTo h₁ ht, heq, upTo_upTo h₂ ht]

/-! ### Looking up nodes -/

theorem get?_cons (x y : NodeId) (n : Node V) (P : Struct V) :
    Struct.get? ((y, n) :: P) x = if x = y then some n else P.get? x := by
  simp only [Struct.get?, List.lookup_cons]
  by_cases h : x = y
  · subst h; simp
  · have : (x == y) = false := by simp [h]
    simp [this, h]

@[simp] theorem get?_nil (x : NodeId) : Struct.get? ([] : Struct V) x = none := rfl

theorem get?_append (P Q : Struct V) (x : NodeId) :
    (P ++ Q).get? x = (P.get? x).or (Q.get? x) := by
  simp [Struct.get?, List.lookup_append]

theorem mem_of_get? {P : Struct V} {x : NodeId} {n : Node V} (h : P.get? x = some n) :
    (x, n) ∈ P := by
  induction P with
  | nil => simp at h
  | cons p P ih =>
    obtain ⟨y, m⟩ := p
    rw [get?_cons] at h
    by_cases hxy : x = y
    · subst hxy; simp at h; subst h; simp
    · simp [hxy] at h; exact List.mem_cons_of_mem _ (ih h)

theorem get?_isSome_of_mem {P : Struct V} {x : NodeId} {n : Node V} (h : (x, n) ∈ P) :
    (P.get? x).isSome := by
  induction P with
  | nil => simp at h
  | cons p P ih =>
    obtain ⟨y, m⟩ := p
    rw [get?_cons]
    by_cases hxy : x = y
    · simp [hxy]
    · simp only [hxy, ite_false]
      simp at h
      rcases h with ⟨h1, _⟩ | h
      · exact absurd h1 hxy
      · exact ih h

theorem get?_addEntry (P : Struct V) (i : Time) (y : NodeId) (v : V) (x : NodeId) :
    (P.addEntry i y v).get? x =
      (P.get? x).map (fun n => if x = y then { n with hist := n.hist ++ [⟨i, v⟩] } else n) := by
  induction P with
  | nil => rfl
  | cons p P ih =>
    obtain ⟨z, m⟩ := p
    simp only [Struct.addEntry, List.map_cons] at ih ⊢
    by_cases hzy : z = y
    · subst hzy
      simp only [ite_true]
      rw [get?_cons, get?_cons]
      by_cases hxz : x = z
      · subst hxz; simp
      · simp [hxz, ih]
    · simp only [hzy, ite_false]
      rw [get?_cons, get?_cons]
      by_cases hxz : x = z
      · subst hxz; simp [hzy]
      · simp [hxz, ih]

/-- The entries that changes c add to node x at time i. -/
def addsFor (c : Changes V) (i : Time) (x : NodeId) : History V :=
  (c.adds.filter (fun a => a.1 == x)).map (fun a => ⟨i, a.2⟩)

theorem get?_foldl_addEntry (adds : List (NodeId × V)) (P : Struct V) (i : Time) (x : NodeId) :
    (adds.foldl (fun P a => P.addEntry i a.1 a.2) P).get? x =
      (P.get? x).map (fun n =>
        { n with hist := n.hist ++ (adds.filter (fun a => a.1 == x)).map (fun a => ⟨i, a.2⟩) }) := by
  induction adds generalizing P with
  | nil => cases h : P.get? x <;> simp [h]
  | cons a adds ih =>
    simp only [List.foldl_cons]
    rw [ih, get?_addEntry]
    cases h : P.get? x with
    | none => simp
    | some n =>
      simp only [Option.map_some]
      by_cases hx : x = a.1
      · subst hx; simp
      · have : (a.1 == x) = false := by simp; exact fun h => hx h.symm
        simp [hx, this]

/-- The node that changes c create with id x, as a node of P. -/
def newNodeOf (c : Changes V) (x : NodeId) : Option (Node V) :=
  Struct.get? (c.new.map (fun n => (n.id, ({ level := n.level, isData := n.isData, hist := [] } : Node V)))) x

theorem get?_apply (P : Struct V) (i : Time) (c : Changes V) (x : NodeId) :
    (P.apply i c).get? x =
      ((P.get? x).or (newNodeOf c x)).map (fun n => { n with hist := n.hist ++ addsFor c i x }) := by
  simp only [Struct.apply]
  rw [get?_foldl_addEntry, get?_append]
  rfl

/-- A node of P, after the changes: same level and kind, entries added at the end. -/
theorem get?_apply_of_get? {P : Struct V} {i : Time} {c : Changes V} {x : NodeId} {n : Node V}
    (h : P.get? x = some n) :
    (P.apply i c).get? x = some { n with hist := n.hist ++ addsFor c i x } := by
  rw [get?_apply, h]; rfl

theorem mem_addsFor {c : Changes V} {i : Time} {x : NodeId} {e : Entry V} :
    e ∈ addsFor c i x ↔ e.time = i ∧ (x, e.val) ∈ c.adds := by
  simp only [addsFor, List.mem_map, List.mem_filter, beq_iff_eq]
  constructor
  · rintro ⟨a, ⟨ha, hx⟩, rfl⟩
    refine ⟨rfl, ?_⟩
    subst hx
    simpa using ha
  · rintro ⟨ht, hm⟩
    exact ⟨(x, e.val), ⟨hm, rfl⟩, by cases e; simp_all⟩

/-! ### Structures that agree on every node -/

/-- P and P' have the same node for every id. -/
def SameNodes (P P' : Struct V) : Prop := ∀ x, P.get? x = P'.get? x

theorem SameNodes.refl (P : Struct V) : SameNodes P P := fun _ => rfl
theorem SameNodes.symm {P P' : Struct V} (h : SameNodes P P') : SameNodes P' P := fun x => (h x).symm

theorem SameNodes.apply {P P' : Struct V} (h : SameNodes P P') (i : Time) (c : Changes V) :
    SameNodes (P.apply i c) (P'.apply i c) := by
  intro x; rw [get?_apply, get?_apply, h x]

end SIS
