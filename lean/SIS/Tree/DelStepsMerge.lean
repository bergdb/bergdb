/-
Case (4)'s delete steps with the merges on (bergdb 024-12, TP7 and TP10): the
delete splits as the merges-off cases (5) to (9) do: no leaf, a noop, a leaf
that empties (the upward delete), a leaf that keeps a live klong with room for
the bitmap, or full (`DelNoLeafM` to `DelFullM`, `delMerge_cover`). The reading's
cases are in DelSteps.lean, the take-back's in TakeDelSteps.lean.
-/
import SIS.Tree.TakeDelMerge
import SIS.Tree.GetCaseBridge

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! ## The delete's cases with the merges on -/

/-- A delete, the merges on, of a key that has no leaf. -/
def DelNoLeafM (c : Ctx) (base : View BVal) (w : W) (op : Op) : Prop :=
  ∃ key, op = .del key ∧ c.p.merges = true ∧ ¬ ∃ pre cv L n, key = pre ++ [cv] ∧ KeyLeaf c base w pre cv L n

/-- A delete, the merges on, whose bitmap changes nothing. -/
def DelNoopM (c : Ctx) (base : View BVal) (w : W) (op : Op) : Prop :=
  ∃ pre cv L n, op = .del (pre ++ [cv]) ∧ c.p.merges = true ∧ KeyLeaf c base w pre cv L n ∧
    bitsUnion n.lastBitmap (n.bitsOf cv) = n.lastBitmap

/-- A delete, the merges on, that empties its leaf: the upward delete. -/
def DelEmptyM (c : Ctx) (base : View BVal) (w : W) (op : Op) : Prop :=
  ∃ pre cv L n, op = .del (pre ++ [cv]) ∧ c.p.merges = true ∧ KeyLeaf c base w pre cv L n ∧
    bitsUnion n.lastBitmap (n.bitsOf cv) ≠ n.lastBitmap ∧
    n.allKeysIn (bitsUnion n.lastBitmap (n.bitsOf cv)) = true

/-- A delete, the merges on, whose leaf keeps a live klong and has room for the
bitmap. -/
def DelRoomM (c : Ctx) (base : View BVal) (w : W) (op : Op) : Prop :=
  ∃ pre cv L n, op = .del (pre ++ [cv]) ∧ c.p.merges = true ∧ KeyLeaf c base w pre cv L n ∧
    bitsUnion n.lastBitmap (n.bitsOf cv) ≠ n.lastBitmap ∧
    n.allKeysIn (bitsUnion n.lastBitmap (n.bitsOf cv)) = false ∧ DelRoom c cv n

/-- A delete, the merges on, whose leaf keeps a live klong and is full. -/
def DelFullM (c : Ctx) (base : View BVal) (w : W) (op : Op) : Prop :=
  ∃ pre cv L n, op = .del (pre ++ [cv]) ∧ c.p.merges = true ∧ KeyLeaf c base w pre cv L n ∧
    bitsUnion n.lastBitmap (n.bitsOf cv) ≠ n.lastBitmap ∧
    n.allKeysIn (bitsUnion n.lastBitmap (n.bitsOf cv)) = false ∧ ¬ DelRoom c cv n

/-- Every delete with the merges on is in one of the five cases. -/
theorem delMerge_cover (c : Ctx) (base : View BVal) (w : W) (key : Key) (hm : c.p.merges = true) :
    DelNoLeafM c base w (.del key) ∨ DelNoopM c base w (.del key) ∨ DelEmptyM c base w (.del key) ∨
    DelRoomM c base w (.del key) ∨ DelFullM c base w (.del key) := by
  by_cases hk : ∃ pre cv L n, key = pre ++ [cv] ∧ KeyLeaf c base w pre cv L n
  · obtain ⟨pre, cv, L, n, hkey, hl⟩ := hk
    subst hkey
    by_cases hb : bitsUnion n.lastBitmap (n.bitsOf cv) = n.lastBitmap
    · exact Or.inr (Or.inl ⟨pre, cv, L, n, rfl, hm, hl, hb⟩)
    · cases ha : n.allKeysIn (bitsUnion n.lastBitmap (n.bitsOf cv)) with
      | true => exact Or.inr (Or.inr (Or.inl ⟨pre, cv, L, n, rfl, hm, hl, hb, ha⟩))
      | false =>
        by_cases hr : DelRoom c cv n
        · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨pre, cv, L, n, rfl, hm, hl, hb, ha, hr⟩)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨pre, cv, L, n, rfl, hm, hl, hb, ha, hr⟩)))
  · exact Or.inl ⟨key, rfl, hm, hk⟩

/-! ## The obligations by case -/

/-! ## The read-only cases -/

end SIS.Tree
