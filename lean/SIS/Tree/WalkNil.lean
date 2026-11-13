/-
The tree model (bergdb 024-12, TP6 and TP7): what a fault-free step of the
invariants' walk says, as an equivalence. The walk's checks of one key node
are of two kinds:

* of the node as it is now, whatever the time of the walk (`CurrentOK`): its
  size, well-formed klongs, klongs that give its history, pointers to nodes
  of P, the bound on dead klongs;
* of the node's live klongs at the walk's time (`TimeOK`): a live klong, the
  empty key first, two live klongs in an inner root, the fill, the order.

With them and the faults of the children (`walkChildFaults`), a step of the
walk without faults is a conjunction (`walk_succ_eq_nil_iff`). Proofs that
build a fault-free walk, and proofs that take one apart, start here.
-/
import SIS.Tree.WalkComplete
import SIS.Tree.NodeKinds
import SIS.Tree.SegmentRange

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- The key node that the walk reads from a node of P. -/
def nodeK (p : Params) (nd : Node BVal) : KNode :=
  ⟨p.heightOf nd.level == 0, klongsOf nd.hist⟩

/-- A live compare value is within the bounds of its node, as the walk tests
it (`RangeOK`). -/
def cvInRange (leaf : Bool) (lo : Nat) (hi : Option Nat) (c : Nat) : Bool :=
  (if leaf then decide (lo ≤ c) else (c == 0 || decide (lo < c))) &&
  (match hi with
    | some b => decide (c < b)
    | none => true)

/-- The walk's checks of a key node as it is now, at whatever time the walk
looks: `SizeOK`, `klongsWf`, klongs that give the history, `PointersOK` of its
klongs, `DeadOK`. -/
def CurrentOK (p : Params) (v : View BVal) (nd : Node BVal) : Prop :=
  (nodeK p nd).size ≤ p.M ∧ klongsWf (nodeK p nd).ks = true ∧
  entriesOf (nodeK p nd).ks = nd.hist ∧
  (∀ c y, Klong.key c y ∈ (nodeK p nd).ks → (v y).isSome = true) ∧
  (p.theta ≠ 0 → (nodeK p nd).deadCount ≤ p.theta)

/-- The walk's checks of a key node's live klongs at the walk's time:
`NonEmptyOK`, `LeftmostOK`, `RootsOK`, `FillOK`, `RangeOK`. They read the
node's kind and its live klongs only. -/
def TimeOK (p : Params) (leaf : Bool) (live : List (Nat × NodeId)) (lo : Nat)
    (hi : Option Nat) (isRoot space : Bool) : Prop :=
  (live.isEmpty && !(space && isRoot && leaf)) = false ∧
  (!leaf && !live.isEmpty && (live.head?.map (·.1)) != some 0) = false ∧
  (!leaf && isRoot && decide (live.length < 2)) = false ∧
  (p.merges && !isRoot && decide (live.length < p.mergeBelow)) = false ∧
  ∀ q ∈ live, cvInRange leaf lo hi q.1 = true

theorem ite_fault_nil_iff {c : Prop} [Decidable c] (s : String) :
    (if c then [s] else ([] : Faults)) = [] ↔ ¬ c := by
  by_cases h : c <;> simp [h]

theorem ite_none_iff {c : Bool} (s : String) :
    (if c = true then none else some s) = none ↔ c = true := by
  cases c <;> simp

/-- A step of the walk at a key node finds no fault exactly when the node is
sound as it is now, its live klongs are sound at the time, and no child has a
fault. -/
theorem walk_succ_eq_nil_iff (p : Params) (v : View BVal) (t f : Nat) (x lo : Nat)
    (hi : Option Nat) (isRoot space : Bool) (nd : Node BVal)
    (hv : v x = some nd) (hd : nd.isData = false) :
    walk p v t (f+1) x lo hi isRoot space = [] ↔
      CurrentOK p v nd ∧
      TimeOK p (nodeK p nd).leaf ((nodeK p nd).liveAt t) lo hi isRoot space ∧
      ∀ qb ∈ childBounds ((nodeK p nd).liveAt t) hi,
        walkChildFaults p v t f x (nodeK p nd) (p.segOf nd.level)
          (p.heightOf nd.level) lo space qb = [] := by
  rw [walk]
  simp only [hv, hd, Bool.false_eq_true, ↓reduceIte]
  rw [List.append_eq_nil_iff]
  constructor
  · rintro ⟨hown, hbelow⟩
    simp only [List.append_eq_nil_iff, ite_fault_nil_iff, List.filterMap_eq_nil_iff] at hown
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := hown
    refine ⟨⟨Nat.le_of_not_lt h1, by simpa [nodeK] using h2, by simpa [nodeK] using h3, ?_, ?_⟩,
      ⟨Bool.eq_false_iff.mpr h5, Bool.eq_false_iff.mpr h6, Bool.eq_false_iff.mpr h7,
        Bool.eq_false_iff.mpr h8, ?_⟩, ?_⟩
    · intro c y hk
      have h := h4 _ hk
      cases hy : v y with
      | some ny => rfl
      | none => simp [hy] at h
    · intro h0
      simp only [Bool.and_eq_true, bne_iff_ne, decide_eq_true_eq, not_and, Nat.not_lt] at h9
      exact h9 h0
    · intro q hq
      exact (ite_none_iff _).mp (h10 q hq)
    · exact List.flatMap_eq_nil_iff.mp hbelow
  · rintro ⟨⟨a1, a2, a3, a4, a5⟩, ⟨b1, b2, b3, b4, b5⟩, hc⟩
    refine ⟨?_, List.flatMap_eq_nil_iff.mpr hc⟩
    simp only [List.append_eq_nil_iff, ite_fault_nil_iff, List.filterMap_eq_nil_iff]
    refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨Nat.not_lt_of_ge a1, by simpa [nodeK] using a2⟩, by simpa [nodeK] using a3⟩, ?_⟩,
      Bool.eq_false_iff.mp b1⟩, Bool.eq_false_iff.mp b2⟩, Bool.eq_false_iff.mp b3⟩,
      Bool.eq_false_iff.mp b4⟩, ?_⟩, ?_⟩
    · intro k hk
      cases k with
      | key c y =>
        have h := a4 c y hk
        cases hy : v y with
        | some ny => simp [hy]
        | none => simp [hy] at h
      | time u => rfl
      | del bits => rfl
    · simp only [Bool.and_eq_true, bne_iff_ne, decide_eq_true_eq, not_and, Nat.not_lt]
      exact a5
    · intro q hq
      exact (ite_none_iff _).mpr (b5 q hq)

end SIS.Tree
