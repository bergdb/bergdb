/-
The contract package (bergdb 030-04): the order of keys and of positions.
`keyLt` (Read.lean) is the order `<` of lists of compare values; a position
(`Pos`: Java's -1, a compare value, `Long.MAX_VALUE`) is ordered with `lo`
below and `hi` above every compare value.
-/
import Mathlib.Tactic
import Mathlib.Order.WithBot
import Contract.Statement

namespace Contract

/-- A position as a number, or below or above every number. -/
def Pos.rank : Pos → WithBot (WithTop Nat)
  | .lo => ⊥
  | .at c => ((c : WithTop Nat) : WithBot (WithTop Nat))
  | .hi => ((⊤ : WithTop Nat) : WithBot (WithTop Nat))

theorem Pos.rank_injective : Function.Injective Pos.rank := by
  intro a b h
  cases a <;> cases b <;> simp [Pos.rank] at h <;> simp [h]

theorem rank_lt_top (c : Nat) :
    ((c : WithTop Nat) : WithBot (WithTop Nat)) < (⊤ : WithBot (WithTop Nat)) := by
  rw [← WithBot.coe_top]
  exact WithBot.coe_lt_coe.mpr (WithTop.coe_lt_top c)

instance : LinearOrder Pos := LinearOrder.lift' Pos.rank Pos.rank_injective

theorem Pos.lt_def (a b : Pos) : a < b ↔ a.rank < b.rank := Iff.rfl
theorem Pos.le_def (a b : Pos) : a ≤ b ↔ a.rank ≤ b.rank := Iff.rfl

@[simp] theorem Pos.at_lt_at {c d : Nat} : Pos.at c < Pos.at d ↔ c < d := by
  simp [Pos.lt_def, Pos.rank]

@[simp] theorem Pos.at_le_at {c d : Nat} : Pos.at c ≤ Pos.at d ↔ c ≤ d := by
  simp [Pos.le_def, Pos.rank]

@[simp] theorem Pos.lo_lt_at {c : Nat} : Pos.lo < Pos.at c := by
  simp [Pos.lt_def, Pos.rank]

@[simp] theorem Pos.at_lt_hi {c : Nat} : Pos.at c < Pos.hi := by
  simp [Pos.lt_def, Pos.rank, rank_lt_top]

theorem Pos.below_iff (p : Pos) (c : Nat) : p.below c = true ↔ p < Pos.at c := by
  cases p <;> simp [Pos.below, Pos.lt_def, Pos.rank]

theorem Pos.above_iff (p : Pos) (c : Nat) : p.above c = true ↔ Pos.at c < p := by
  cases p <;> simp [Pos.above, Pos.lt_def, Pos.rank, rank_lt_top]

theorem Pos.is_iff (p : Pos) (c : Nat) : p.is c = true ↔ p = Pos.at c := by
  cases p <;> simp [Pos.is]
  exact eq_comm

/-- A key as a list of positions. -/
def kp (k : Key) : List Pos := k.map Pos.at

theorem kp_lt_iff : ∀ (k₁ k₂ : Key), kp k₁ < kp k₂ ↔ k₁ < k₂
  | [], [] => by simp [kp]
  | [], b :: l₂ => by simp [kp]
  | a :: l₁, [] => by simp [kp]
  | a :: l₁, b :: l₂ => by
    have ih := kp_lt_iff l₁ l₂
    simp only [kp, List.map_cons, List.cons_lt_cons_iff, Pos.at_lt_at, Pos.at.injEq] at ih ⊢
    rw [ih]

theorem kp_injective : Function.Injective kp := by
  intro a b h
  simp only [kp] at h
  exact List.map_injective_iff.mpr (fun x y hxy => by injection hxy) h

theorem keyLt_iff : ∀ (k₁ k₂ : Key), keyLt k₁ k₂ = true ↔ k₁ < k₂
  | [], [] => by simp [keyLt]
  | [], b :: l₂ => by simp [keyLt]
  | a :: l₁, [] => by simp [keyLt]
  | a :: l₁, b :: l₂ => by
    have ih := keyLt_iff l₁ l₂
    simp only [keyLt, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq,
      List.cons_lt_cons_iff]
    rw [ih]

theorem keyLt_false_iff (k₁ k₂ : Key) : keyLt k₁ k₂ = false ↔ k₂ ≤ k₁ := by
  rw [← not_lt, ← keyLt_iff]
  simp

/-- Lists that share a front are in the order of what follows it. -/
theorem append_lt_append_iff {α : Type} [LinearOrder α] (pre : List α) (a b : List α) :
    pre ++ a < pre ++ b ↔ a < b := by
  induction pre with
  | nil => simp
  | cons x r ih => simp [ih]

theorem append_le_append_iff {α : Type} [LinearOrder α] (pre : List α) (a b : List α) :
    pre ++ a ≤ pre ++ b ↔ a ≤ b := by
  rw [← not_lt, ← not_lt, append_lt_append_iff]

theorem cons_lt_cons_of_lt {α : Type} [LinearOrder α] {a b : α} (h : a < b) (l₁ l₂ : List α) :
    a :: l₁ < b :: l₂ :=
  List.cons_lt_cons_iff.mpr (Or.inl h)

theorem singleton_le_cons {α : Type} [LinearOrder α] (a : α) (l : List α) : [a] ≤ a :: l := by
  cases l with
  | nil => exact le_refl _
  | cons b r => exact le_of_lt (List.cons_lt_cons_iff.mpr (Or.inr ⟨rfl, List.nil_lt_cons b r⟩))

end Contract
