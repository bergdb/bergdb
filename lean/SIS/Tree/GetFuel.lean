import SIS.Tree.GetCascadeIP

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! The reader's fuel (bergdb 024-12, TP10): `getFromR` gives each segment's
descent the same fuel (`Params.fuel`, from G and H). Once every descent fits in
it, more fuel gives the same answer (`getFromR_fuel_mono`): the fuel is then no
restriction of the model. A split that makes a new root grows a segment's tree
by a level; its reading needs one level of room (`SegDepthLe` below the fuel). -/

/-- The segment tree of x has depth at most d: a node at depth 0 is a segment
leaf, an inner node's live children have depth at most d - 1. -/
def SegDepthLe (N : NodeId → Option KNode) (t : Time) : Nat → NodeId → Prop
  | 0, x => ∀ n, N x = some n → n.leaf = true
  | d + 1, x => ∀ n, N x = some n → n.leaf = false → ∀ c y, (c, y) ∈ n.liveAt t → SegDepthLe N t d y

theorem SegDepthLe.mono (N : NodeId → Option KNode) (t : Time) :
    ∀ d x, SegDepthLe N t d x → ∀ d', d ≤ d' → SegDepthLe N t d' x := by
  intro d
  induction d with
  | zero =>
    intro x h d' _
    cases d' with
    | zero => exact h
    | succ d' => intro n hn hl; rw [h n hn] at hl; cases hl
  | succ d ih =>
    intro x h d' hd
    cases d' with
    | zero => omega
    | succ d' =>
      intro n hn hl c y hy
      exact ih y (h n hn hl c y hy) d' (by omega)

/-- Once the descent fits, the fuel does not change what it finds. -/
theorem getEqR_fuel_mono (N : NodeId → Option KNode) (t : Time) (cv : Nat) :
    ∀ d x, SegDepthLe N t d x → ∀ f f', d < f → d < f' →
      getEqR N t cv f x = getEqR N t cv f' x := by
  intro d
  induction d with
  | zero =>
    intro x h f f' hf hf'
    obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    obtain ⟨f', rfl⟩ : ∃ g, f' = g + 1 := ⟨f' - 1, by omega⟩
    simp only [getEqR]
    cases hn : N x with
    | none => rfl
    | some n => simp only [h n hn, ↓reduceIte]
  | succ d ih =>
    intro x h f f' hf hf'
    obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    obtain ⟨f', rfl⟩ : ∃ g, f' = g + 1 := ⟨f' - 1, by omega⟩
    simp only [getEqR]
    cases hn : N x with
    | none => rfl
    | some n =>
      simp only
      cases hl : n.leaf with
      | true => rfl
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        cases hs : n.searchLte t cv with
        | none => rfl
        | some fd =>
          simp only
          exact ih fd.y (h n hn hl fd.c fd.y (KNode.searchLte_mem n t cv fd hs)) f f' (by omega)
            (by omega)

/-- Every segment tree reached from r has depth at most d. -/
def SegFits (N : NodeId → Option KNode) (t : Time) (d : Nat) (r : NodeId) : Prop :=
  ∀ x, ReachS N t r x → SegDepthLe N t d x

/-- With more fuel `getFromR` gives the same answer once every descent fits. -/
theorem getFromR_fuel_mono (N : NodeId → Option KNode) (V : NodeId → Option Nat) (t : Time)
    (d : Nat) (r0 : NodeId) (hwf : ∀ x xn, ReachS N t r0 x → N x = some xn → klongsWf xn.ks = true)
    (hfit : SegFits N t d r0) (f f' : Nat) (hf : d < f) (hf' : d < f') :
    ∀ key r, ReachS N t r0 r → getFromR N V t f key r = getFromR N V t f' key r := by
  intro key
  induction key with
  | nil => intro r _; rfl
  | cons c rest ih =>
    intro r hr
    have he := getEqR_fuel_mono N t c d r (hfit r hr) f f' hf hf'
    cases rest with
    | nil => simp only [getFromR]; rw [he]
    | cons e rest' =>
      simp only [getFromR]
      rw [← he]
      cases hg : getEqR N t c f r with
      | none => rfl
      | some y =>
        simp only
        split
        · exact ih y (getEqR_reach N t r0 c hwf f r y hr hg)
        · rfl

end SIS.Tree
